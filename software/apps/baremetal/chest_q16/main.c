// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_chest_q16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_chest_q16.h"

/*
======================
Parameters and defines

SINGLE: When defined runs single-core Channel Estimation.
PARALLEL: When defined runs parallel Channel Estimation.
*/

#define PARALLEL

int16_t l1_PilotTX[2 * N_TX * N_SAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
int16_t l1_PilotRX[2 * N_RX * N_SAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
int16_t l1_HEST[2 * N_RX * N_TX * N_SAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_PilotRX, l2_PilotRX,
                        (N_RX * N_SAMPLES) * sizeof(int32_t));
    dma_memcpy_blocking(l1_PilotTX, l2_PilotTX,
                        (N_TX * N_SAMPLES) * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  /* Kernel */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_chest_q16s_unrolled4(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX, N_TX,
                                 N_SAMPLES);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif
#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_chest_q16p_unrolled4(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX, N_TX,
                               N_SAMPLES, core_id, num_cores);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
#endif

  /* Check */
  mempool_check_i16(l1_HEST, l2_HEST, 2 * N_TX * N_RX, 0, 0);
  mempool_barrier(num_cores);
  return 0;
}
