// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yichao Zhang, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_axpy_i32.h"

#include "baremetal/mempool_axpy_i32.h"
#include "baremetal/mempool_checks.h"

int32_t l1_X[array_N] __attribute__((aligned(NUM_BANKS), section(".l1")));
int32_t l1_Y[array_N] __attribute__((aligned(NUM_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));

int main() {

  uint32_t const core_id = mempool_get_core_id();
  uint32_t const num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  // Initialize data
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, array_N * sizeof(int32_t));
    dma_memcpy_blocking(l1_Y, l2_Y, array_N * sizeof(int32_t));
    error = 0;
  }
  register volatile int32_t a = l2_A;
  mempool_barrier(num_cores);

  // Benchmark
  mempool_start_benchmark();
  calc_axpy_unloop_x4_localbank(l1_X, l1_Y, a, array_N, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Verify results
  mempool_check_i32(l1_Y, l2_Z, array_N, 0, 0);
  mempool_barrier(num_cores);

  return 0;
}
