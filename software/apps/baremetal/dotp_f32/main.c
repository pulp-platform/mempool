// Copyright 2021 ETH Zurich and University of Bologna.
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

#include "data_dotp_f32.h"
uint32_t red_barrier[NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

#include "baremetal/mempool_dotp_f32.h"

float l1_X[array_N] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float l1_Y[array_N] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float sum[NUM_BANKS] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time_init, time_end;
  mempool_barrier_init(core_id);

  time_init = 0;
  time_end = 0;
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, array_N * sizeof(int32_t));
    dma_memcpy_blocking(l1_Y, l2_Y, array_N * sizeof(int32_t));
  }
  for (uint32_t k = core_id; k < NUM_BANKS; k += num_cores) {
    sum[k] = 0;
    red_barrier[k] = 0;
  }
  mempool_barrier(num_cores);

  // PARALLEL, LOCAL ACCESSES
  time_init = mempool_get_timer();
  dotp_f32p_local_unrolled4(l1_X, l1_Y, sum, array_N);
  time_end = mempool_get_timer();

  // Check results
  mempool_barrier(num_cores);
  if (core_id == 0) {
    uint32_t clock_cycles = (time_end - time_init);
    printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
    printf("Result ==> %d\n", sum[0]);
    printf("Check  ==> %d\n\n", l2_Z);
  }
  mempool_barrier(num_cores);

  return 0;
}
