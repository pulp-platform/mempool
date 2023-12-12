// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data_cmatmul_f16.h"
#include "kernel/mempool_checks.h"
#include "kernel/mempool_cmatmul_f16.h"
#define PARALLEL_2x2

__fp16 matrix_a[2 * dim_M * dim_N]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 matrix_b[2 * dim_N * dim_P]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 matrix_c[2 * dim_M * dim_P]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 matrix_a_folded[2 * dim_M * (4 * NUM_CORES)]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, A, dim_M * dim_N * sizeof(int32_t));
    dma_memcpy_blocking(matrix_b, B, dim_N * dim_P * sizeof(int32_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#if defined(SINGLE)
  // Execute function to test.
  if (core_id == 0) {
    mempool_start_benchmark();
    cmatmul_2x4_f16s(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL_2x2)
  // Execute function to test.
  uint32_t nPE = core_id < (dim_P / 2) ? num_cores : (dim_P / 2);
  if (core_id < nPE) {
    mempool_start_benchmark();
    cmatmul_2x2_f16p(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P, core_id,
                     nPE);
    mempool_log_partial_barrier(2, core_id, nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL_2x4)
  // Execute function to test.
  uint32_t nPE = core_id < (dim_P / 4) ? num_cores : (dim_P / 4);
  if (core_id < nPE) {
    mempool_start_benchmark();
    cmatmul_2x4_f16p(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P, core_id,
                     nPE);
    mempool_log_partial_barrier(2, core_id, nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(TEST)
  mempool_check_f32(matrix_c, C, 2 * dim_M * dim_P, 0.01f, 0);
  mempool_barrier(num_cores);
#endif

  return 0;
}
