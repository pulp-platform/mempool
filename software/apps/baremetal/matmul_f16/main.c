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

#include "data_matmul_f16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_matmul_f16.h"

/*
======================
Parameters and defines

SINGLE: When defined runs single-core matmul.
PARALLEL: When defined runs parallel matmul.
*/

__fp16 matrix_a[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 matrix_b[matrix_N * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 matrix_c[matrix_M * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices 1
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, l2_A,
                        (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(matrix_b, l2_B,
                        (matrix_N * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

#if defined(SINGLE)
  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    matmul_2x2_single_f16(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                          matrix_P);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL)
  // Execute function to test.
  mempool_start_benchmark();
  matmul_4x2_parallel_f16vec(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                             matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  mempool_check_f16(matrix_c, l2_C, matrix_M * matrix_P, 0.5f, 0);
  mempool_barrier(num_cores);
  return 0;
}
