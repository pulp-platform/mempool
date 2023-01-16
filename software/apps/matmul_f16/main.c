// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_matmulf16.h"
#include "kernel/mat_mul_f16.h"

#define PARALLEL

float16 matrix_a[matrix_M * matrix_N] __attribute__((aligned((matrix_M * matrix_N)/2), section(".l1")));
float16 matrix_b[matrix_N * matrix_P] __attribute__((aligned((matrix_N * matrix_P)/2), section(".l1")));
float16 matrix_c[matrix_M * matrix_P] __attribute__((aligned((matrix_M * matrix_P)/2), section(".l1")));

int volatile error __attribute__((section(".l1")));

void init_matrix(float16 *matrix, float16 *input, uint32_t num_rows,
                 uint32_t num_columns, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < (num_columns * num_rows); i += num_cores) {
    matrix[i] = (float16) input[i];
  }
}

int verify_result(float16 *__restrict__ C, float16 *__restrict__ Exp, uint32_t M,
                  uint32_t P, uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < M * P; i++) {
      float16 error = (float16) 0.0f;
      float16 exp = (float16) Exp[i];
      float16 res = (float16) C[i];
      //printf("%d %d\n", (int32_t) exp, (int32_t) res);
      asm volatile("fsub.h %[error], %[res], %[exp];"
                   : [error] "+&r"(error)
                   : [res] "r"(res), [exp] "r"(exp));
      if ((int32_t) error != 0) {
        printf("ERROR!!! %d %d\n", i, error);
      }
    }
    // Wait at barrier before checking
    mempool_barrier(num_cores);
  }
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
  }

  // Initialize Matrices
  init_matrix(matrix_a, A, matrix_M, matrix_N, core_id, num_cores);
  init_matrix(matrix_b, B, matrix_N, matrix_P, core_id, num_cores);
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#if defined(PARALLEL)
  // Execute function to test.
  mempool_start_benchmark();
  matmul_2x2_parallel_f16_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
                                matrix_N, matrix_P, core_id, num_cores);
  //matmul_4x4_parallel_f16_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
  //                              matrix_N, matrix_P, core_id, num_cores);
  //dump_id(core_id);
  mempool_stop_benchmark();
  // Wait at barrier before checking
  mempool_barrier(num_cores);
#elif defined(SINGLE)
  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    matmul_2x2_single_f16_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
                                matrix_N, matrix_P);
    mempool_stop_benchmark();
  }
  // Wait at barrier before checking
  mempool_barrier(num_cores);
#endif

  verify_result(matrix_c, C, matrix_M, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);

  return error;
}
