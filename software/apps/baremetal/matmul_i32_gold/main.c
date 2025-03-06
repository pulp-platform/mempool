// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]

#include <stdint.h>
#include <string.h>

#include "data_matmul_i32.h"

#include "baremetal/mat_mul_conflict_opt.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

int32_t matrix_a[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
int32_t matrix_b[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));
int32_t matric_c_gold[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

int volatile error __attribute__((section(".l1")));

// Initialize the matrices in parallel
void verify_matrix(int32_t *__restrict__ pRes, int32_t *__restrict__ pExp,
                   uint32_t NEL, uint32_t id, uint32_t numThreads) {
  uint32_t const n_start = id * NEL / numThreads;
  uint32_t const n_end = (id + 1) * NEL / numThreads;
  for (uint32_t i = n_start; i < n_end; i++) {
    if (pRes[i] != pExp[i]) {
      error = 1;
      return;
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, A, matrix_M * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(matrix_b, B, matrix_N * matrix_P * sizeof(int32_t));
    dma_memcpy_blocking(matric_c_gold, C,
                        matrix_M * matrix_P * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  mempool_start_benchmark();
  mat_mul_unrolled_4x4_parallel_asm(matrix_a, matrix_b, matrix_c, matrix_M,
                                    matrix_N, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Test the Matrix multiplication
  verify_matrix(matrix_c, matric_c_gold, matrix_M * matrix_P, core_id,
                num_cores);
  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
