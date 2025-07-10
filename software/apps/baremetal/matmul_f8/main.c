// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_matmul_f8.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_matmul_f8.h"

/*
======================
Parameters and defines

INNER: When defined runs inner product based matmul.
OUTER: When defined runs outer product based matmul.
*/
#define INNER

__fp8 matrix_a[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp8 matrix_b[matrix_N * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp8 matrix_c[matrix_M * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // uint32_t num_cores = 64;
  //  Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, l2_A, (matrix_M * matrix_N) * sizeof(int8_t));
    dma_memcpy_blocking(matrix_b, l2_B, (matrix_N * matrix_P) * sizeof(int8_t));
  }
  mempool_barrier(num_cores);

#if defined(INNER)
  // Matmul based on inner product (between rows of A and cols of B)
  mempool_start_benchmark();
  matmul_4x4_parallel_inner_f8vec(matrix_a, matrix_b, matrix_c, matrix_M,
                                  matrix_N, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#if defined(OUTER)
  // Matmul based on outer product (between cols of A and rows of B)
  mempool_start_benchmark();
  matmul_4x4_parallel_outer_f8vec(matrix_a, matrix_b, matrix_c, matrix_M,
                                  matrix_N, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  // For small matrices, replace 150 with matrix_M * matrix_P (dimension of
  // matrix C)
  mempool_check_f8(matrix_c, l2_C, 50, 0x34, 1); // tol = 0.25 = 0x34 (__fp8)
  mempool_barrier(num_cores);
  return 0;
}
