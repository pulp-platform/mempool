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

#include "data/data_chest_f16.h"
#include "kernel/mempool_checks.h"
#include "kernel/mempool_chest_f16.h"

__fp16 l1_PilotTX[2 * N_TX * N_SAMPLES]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1_PilotRX[2 * N_RX * N_SAMPLES]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1_HEST[2 * N_RX * N_TX * N_SAMPLES]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR * sizeof(int32_t)),
                   section(".l1_prio")));

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

  mempool_chest_f16p_unrolled4(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX, N_TX,
                               N_SAMPLES, core_id, num_cores);
  mempool_start_benchmark();
  mempool_chest_f16p_unrolled4(l1_HEST, l1_PilotRX, l1_PilotTX, N_RX, N_TX,
                               N_SAMPLES, core_id, num_cores);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
  return 0;
}
