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

#include "data_cmatmul_f16.h"
#define dim_M (matrix_M)
#define dim_N (matrix_N)
#define dim_P (matrix_P)

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_cmatmul_f16.h"

/*
======================
Parameters and defines

SINGLE_2x2: Single-core matmul on 2x2 tiles.
PARALLEL_2x2: Parallel matmul on 2x2 C-tiles.
PARALLEL_2x4: Parallel matmul on 4x4 C-tiles.
PARALLEL_4x4: Parallel matmul on 4x4 C-tiles.
PARALLEL_4x4_COPIES_A: Parallel matmul on 4x4 C-tiles, compies of A in memory to
avoid banking conflicts.
*/

#if defined(PARALLEL_4x4_COPIES_A)
__fp16 matrix_a[2 * (BANKING_FACTOR * NUM_CORES)]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
#else
__fp16 matrix_a[2 * dim_M * dim_N]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
#endif
__fp16 matrix_b[2 * dim_N * dim_P]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 matrix_c[2 * dim_M * dim_P]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, l2_A, 2 * dim_M * dim_N * sizeof(int16_t));
    dma_memcpy_blocking(matrix_b, l2_B, 2 * dim_N * dim_P * sizeof(int16_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#if defined(SINGLE_2x2)
  // Execute function to test.
  if (core_id == 0) {
    mempool_start_benchmark();
    cmatmul_2x2_f16s(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P);
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
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL_4x4)
  // Execute function to test.
  uint32_t nPE = core_id < (dim_P / 4) ? num_cores : (dim_P / 4);
  if (core_id < nPE) {
    mempool_start_benchmark();
    cmatmul_4x4_f16p(matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P, core_id,
                     nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL_4x4_COPIES_A)
  // Execute function to test.
  mempool_start_benchmark();
  cmatmul_4x4_f16p_copy_A(A, matrix_a, matrix_b, matrix_c, dim_M, dim_N, dim_P,
                          core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  mempool_check_f16(matrix_c, l2_C, 10, 0.1f, 0);
  mempool_barrier(num_cores);
  return 0;
}
