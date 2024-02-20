// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data_cmatmul_q16.h"
#include "kernel/mempool_checks.h"
#include "kernel/mempool_cmatmul_q16.h"

#define PARALLEL

int16_t matrix_a[2 * dim_M * dim_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t matrix_b[2 * dim_N * dim_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t matrix_c[2 * dim_M * dim_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, A, 2 * dim_M * dim_N * sizeof(int16_t));
    dma_memcpy_blocking(matrix_b, B, 2 * dim_N * dim_P * sizeof(int16_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    cmatmul_2x4_q16s(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  mempool_start_benchmark();
  cmatmul_2x4_q16p(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P, core_id,
                   num_cores);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
#endif

  mempool_check_q16(matrix_c, C, 2 * dim_M * dim_P, 16, 0);
  mempool_barrier(num_cores);

  return 0;
}
