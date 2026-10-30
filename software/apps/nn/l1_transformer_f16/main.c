// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "synchronization.h"

// LOG_BARRIER=<r>: the barriers of this app, which all synchronize every core,
// are 2^r-ary tree barriers instead of one counter that every core increments
#ifdef LOG_BARRIER
#include "runtime.h"
#define mempool_barrier(num_cores)                                             \
  mempool_anyradixlog_barrier(LOG_BARRIER, mempool_get_core_id())
#endif

/* Macros to print checkpints of computation */
#define VERBOSE (1)
#define PRINT_DONE(verbose, core_id, num_cores, label)                         \
  do {                                                                         \
    if (verbose) {                                                             \
      if ((core_id) == 0) {                                                    \
        printf("\n\n/* DONE: %s*/\n\n", (label));                              \
      }                                                                        \
      mempool_barrier(num_cores);                                              \
    }                                                                          \
  } while (0)

#include "l2_data.h"

#ifdef PIPELINED
#include "baremetal/mempool_conv1d_f16.h"
#include "baremetal/mempool_layernorm_f16.h"

// The layernorm is the im2col of the convolution that reads it (QKV
// projection, FFN up-projection): it writes its output as an im2col, chunk by
// chunk, so the layernorm of a chunk overlaps with the GEMMs of the previous
// one. conv1d_im2col_t of the layer input X, [Beam][Embed][tdSamples].
static void layernorm_im2col(__fp16 const *__restrict__ X,
                             __fp16 *__restrict__ X_im2col, uint32_t b0,
                             uint32_t nb, uint32_t Ci, uint32_t Wi, uint32_t Wf,
                             uint32_t core_id, uint32_t num_cores) {
  uint32_t cores_per_beam = num_cores / nb;
  uint32_t b = b0 + core_id / cores_per_beam;
  if (b < b0 + nb) {
    layernorm_im2col_w3_parallel_2x4_f16vec(
        &X[b * Ci * Wi], &X_im2col[b * Ci * Wf * Wi], Ci, Wi,
        core_id % cores_per_beam, cores_per_beam);
  }
}
#endif

typedef enum { EBT, TBE } permute_mode_t;
#include "l1_transformer_attention.h"
#include "l1_transformer_ffn.h"

#ifdef CHECKSUM
// CHECKSUM: deterministic input and weights, and a checksum of the output,
// to compare the results of two builds
// fp16 bits of k * 2^-shift, for |k| < 1024 (no float conversion helper)
static uint16_t checksum_fp16(int32_t k, int32_t shift) {
  if (k == 0) {
    return 0;
  }
  uint32_t m = (uint32_t)(k < 0 ? -k : k);
  int32_t e = 31 - __builtin_clz(m);
  return (uint16_t)((k < 0 ? 0x8000u : 0) | ((uint32_t)(e - shift + 15) << 10) |
                    ((m - (1u << e)) << (10 - e)));
}

static void checksum_init(void) {
  for (uint32_t i = 0; i < X_SIZE; i++) {
    *(uint16_t *)&l2_I[i] = checksum_fp16((int32_t)((i * 7919u) % 61u) - 30, 6);
  }
  for (uint32_t i = 0; i < F_SIZE; i++) {
    *(uint16_t *)&l2_F[i] =
        checksum_fp16((int32_t)((i * 104729u) % 37u) - 18, 7);
  }
}

static void checksum_print(__fp16 const *y, int layer) {
  mempool_barrier(mempool_get_core_count());
  if (mempool_get_core_id() == 0) {
    uint32_t h = 0;
    for (uint32_t i = 0; i < X_SIZE; i++) {
      h = h * 31u + *(uint16_t const *)&y[i];
    }
    printf("CHECKSUM layer %d: %x\n", layer, h);
  }
  mempool_barrier(mempool_get_core_count());
}
#define CHECKSUM_PRINT(y, layer) checksum_print((y), (layer))
#else
#define CHECKSUM_PRINT(y, layer)
#endif

int main() {

  // Initialization
  uint32_t core_id = mempool_get_core_id();
  mempool_init(core_id);
  mempool_barrier_init(core_id);
#ifdef CHECKSUM
  if (core_id == 0) {
    checksum_init();
  }
  mempool_barrier(mempool_get_core_count());
#endif

  // Each layer reads the output of the previous one, only the first loads its
  // input from L2
  __fp16 *x;
  x = attention(l2_I, l2_F, NULL, BEAM, EMBED, TDSAMPLES, CONV1D_WF, EBT);
  CHECKSUM_PRINT(x, 1);

  x = ffn(l2_I, l2_F, x, BEAM, EMBED, TDSAMPLES, CONV1D_WF);
  CHECKSUM_PRINT(x, 2);

  x = attention(l2_I, l2_F, x, BEAM, EMBED, TDSAMPLES, CONV1D_WF, TBE);
  CHECKSUM_PRINT(x, 3);

  x = ffn(l2_I, l2_F, x, BEAM, EMBED, TDSAMPLES, CONV1D_WF);
  CHECKSUM_PRINT(x, 4);
  (void)x;

  return 0;
}
