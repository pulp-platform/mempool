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
#include "xpulp/builtins_v2.h"

#include "data/data_chest_q16.h"
#include "kernel/mempool_checks.h"
#include "kernel/mempool_chest_q16p.h"
#include "kernel/mempool_chest_q16s.h"

//#define SINGLE
#define PARALLEL

int16_t l1_PilotTX[2 * N_TX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));
int16_t l1_PilotRX[2 * N_RX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));
int16_t l1_HEST[2 * N_RX * N_TX * N_SAMPLES]
    __attribute__((aligned(N_TX * N_SAMPLES), section(".l1")));

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
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#ifdef SINGLE
  if (core_id == 0) {
    mempool_chest_q16s_unrolled4_xpulpv2(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX,
                                         N_TX, N_SAMPLES);
    mempool_start_benchmark();
    mempool_chest_q16s_unrolled4_xpulpv2(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX,
                                         N_TX, N_SAMPLES);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL

  if (core_id < N_SAMPLES) {
    mempool_chest_q16p_unrolled4_xpulpv2_local(l1_HEST, l1_PilotRX, l1_PilotTX,
                                               N_RX, N_TX, N_SAMPLES, core_id);
    mempool_start_benchmark();
    mempool_chest_q16p_unrolled4_xpulpv2_local(l1_HEST, l1_PilotRX, l1_PilotTX,
                                               N_RX, N_TX, N_SAMPLES, core_id);
    mempool_stop_benchmark();
  }

  mempool_barrier(num_cores);
#endif

  mempool_check_q16(l1_HEST, l2_HEST, 2 * N_RX * N_TX * N_SAMPLES, 100, 0);
  return 0;
}
