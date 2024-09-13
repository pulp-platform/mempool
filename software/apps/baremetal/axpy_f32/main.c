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

#include "data_axpy_f32.h"
#define NUM_BANKS (NUM_CORES * BANKING_FACTOR)

// Vectors for kernel computation
float l1_X[LEN] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float l1_Y[LEN] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

#include "baremetal/mempool_axpy_f32.h"
#include "baremetal/mempool_checks.h"

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time_init, time_end;
  mempool_barrier_init(core_id);

  time_init = 0;
  time_end = 0;
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, LEN * sizeof(int32_t));
    dma_memcpy_blocking(l1_Y, l2_Y, LEN * sizeof(int32_t));
  }
  float register volatile a = A;
  mempool_barrier(num_cores);

  // PARALLEL
  time_init = mempool_get_timer();
  // axpy_f32p(a, l1_X, l1_Y, LEN, num_cores);
  // axpy_f32p_unrolled4(a, l1_X, l1_Y, LEN, num_cores);
  axpy_f32p_local_unrolled4(a, l1_X, l1_Y, LEN);
  time_end = mempool_get_timer();

  // Check results
  if (core_id == 0) {
    uint32_t clock_cycles = (time_end - time_init);
    printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
  }
  mempool_check_f32(l1_Y, l2_out, 100, 0.1f, 0);
  mempool_barrier(num_cores);

  return 0;
}
