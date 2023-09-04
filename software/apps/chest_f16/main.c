// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

#include "data/data_chest_f16.h"

#include "kernel/mempool_chest_f16p.h"
#include "kernel/mempool_chest_f16s.h"

//#define SINGLE
#define PARALLEL

__fp16 PilotTX_l1[2 * N_TX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));
__fp16 PilotRX_l1[2 * N_RX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));
__fp16 HEST_l1[2 * N_RX * N_TX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));

void initialize_vector(__fp16 *pSrc_l2, __fp16 *pDst_l1, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for (uint32_t i = core_id; i < N_el; i += num_cores) {
    pDst_l1[i] = pSrc_l2[i];
  }
  mempool_barrier(num_cores);
  return;
}

void zeros(__fp16 *pSrc_l1, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for (uint32_t i = core_id; i < N_el; i += num_cores) {
    pSrc_l1[i] = (__fp16)0.0f;
  }
  mempool_barrier(num_cores);
  return;
}

void check_result(__fp16 *pDst, __fp16 *l1_pDst, uint32_t N_samples) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if (core_id == 0) {
    printf("Done!\n");
    for (uint32_t i = 0; i < 2 * N_samples; i++) {
      __fp16 exp = pDst[i];
      __fp16 res = l1_pDst[i];
      __fp16 dif;
      float tol = (__fp16)0.05f;
      float dif_f32;
      asm volatile("fsub.h %[dif], %[res], %[exp];"
                   "fcvt.h.s %[dif_f32], %[dif];"
                   : [dif] "+&r"(dif), [dif_f32] "+&r"(dif_f32)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      if ((dif_f32 > tol) || (dif_f32 < (-tol))) {
        printf("%d %x %x\n", i, *(int32_t *)&exp, *(int32_t *)&res);
      }
    }
  }
  mempool_barrier(num_cores);
}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize_vector(PilotRX, PilotRX_l1, 2 * (N_RX * N_SAMPLES));
  initialize_vector(PilotTX, PilotTX_l1, 2 * (N_TX * N_SAMPLES));

#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_chest_f16s_unrolled4(HEST_l1, PilotRX_l1, PilotTX_l1, N_RX, N_TX,
                                 N_SAMPLES);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  // uint32_t nPE = N_SAMPLES < num_cores ? N_SAMPLES : num_cores;
  // if (core_id < N_SAMPLES) {
  mempool_start_benchmark();
  mempool_chest_f16p_unrolled4(HEST_l1, PilotRX_l1, PilotTX_l1, N_RX, N_TX,
                               N_SAMPLES, core_id, num_cores);
  mempool_stop_benchmark();
  //}
  mempool_barrier(num_cores);
#endif

  // check_result(HEST, HEST_l1, (N_TX * N_RX * N_SAMPLES));

  return 0;
}
