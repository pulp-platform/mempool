// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

uint32_t timer_start, timer_end;
// #define GVSOC_TIMING
#define VERBOSE (0)

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "synchronization.h"

#define PRINT_START(verbose, core_id, num_cores, label)                  \
  do {                                                                   \
    if (verbose) {                                                       \
      if ((core_id) == 0) {                                              \
        printf("\n\n\n");                                                \
        printf("/**************************************************/\n");\
        printf("/* START: %s*/\n", (label));                             \
        printf("/**************************************************/\n");\
        printf("\n\n\n");                                                \
      }                                                                  \
      mempool_barrier(num_cores);                                        \
    }                                                                    \
  } while (0)

#define PRINT_DONE(verbose, core_id, num_cores, label)                   \
  do {                                                                   \
    if (verbose) {                                                       \
      if ((core_id) == 0) {                                              \
        printf("/**************************************************/\n");\
        printf("/* DONE: %s*/\n", (label));                              \
        printf("/**************************************************/\n");\
      }                                                                  \
      mempool_barrier(num_cores);                                        \
    }                                                                    \
  } while (0)

#include "l1_transformer_attention.h"
#include "l1_transformer_ffn.h"

int main() {

  // Initialization
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  PRINT_START(VERBOSE, core_id, num_cores, "Attention Time Domain");
  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, TBE);

  PRINT_START(VERBOSE, core_id, num_cores, "Feed-Forward Neural Network");
  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  PRINT_START(VERBOSE, core_id, num_cores, "Attention Embed");
  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, EBT);

  PRINT_START(VERBOSE, core_id, num_cores, "Feed-Forward Neural Network");
  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  return 0;
}
