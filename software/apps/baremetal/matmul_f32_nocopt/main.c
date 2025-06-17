// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_matmul_f32.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_matmul_f32.h"

/*
======================
Parameters and defines

SINGLE: When defined runs single-core matmul.
PARALLEL: When defined runs parallel matmul.
*/

float matrix_a[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
float matrix_b[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
float matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // void (* volatile func_ptr)(float const *__restrict__ A,
  //                            float const *__restrict__ B, float *__restrict__ C,
  //                            uint32_t M, uint32_t N, uint32_t P, uint32_t id,
  //                            uint32_t numThreads) = matmul_4x4_parallel_f32_nocopt_asm;
  mempool_barrier_init(core_id);

  // Initialize data
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, l2_A, matrix_M * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(matrix_b, l2_B, matrix_N * matrix_P * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  // Benchmark
  mempool_start_benchmark();
  // func_ptr(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
  //                            matrix_P, core_id, num_cores);
  matmul_4x4_parallel_f32_nocopt_asm(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                                     matrix_P, core_id, num_cores);
  mempool_start_benchmark();
  mempool_log_barrier(8, core_id);
  mempool_stop_benchmark();

  mempool_check_f32(matrix_c, l2_C, matrix_M * matrix_P, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
