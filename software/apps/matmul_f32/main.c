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

#include "data_matmulf32.h"
#include "kernel/mat_mul_f32.h"

#define PARALLEL

float matrix_a[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
float matrix_b[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
float matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

int volatile error __attribute__((section(".l1")));

void init_matrix(float *matrix, float *input, uint32_t num_rows,
                 uint32_t num_columns, uint32_t core_id, uint32_t num_cores) {

  uint32_t const split = 8; // How many rows/columns to split the matrix into
  if (num_columns > num_rows) {
    // Parallelize over columns
    uint32_t const c_start = (num_rows / split) * (core_id % split);
    uint32_t const c_end = (num_rows / split) * ((core_id % split) + 1);

    for (uint32_t j = (core_id / split); j < num_columns;
         j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        matrix[i * num_columns + j] = input[i * num_columns + j];
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (num_columns / split) * (core_id % split);
    uint32_t const c_end = (num_columns / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < num_rows;
         i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        matrix[i * num_columns + j] = input[i * num_columns + j];
        ;
      }
    }
  }
}

int verify_result(float *__restrict__ C, float *__restrict__ Exp, uint32_t M,
                  uint32_t P, uint32_t core_id, uint32_t num_cores) {

  if (core_id == 0) {
    for (uint32_t i = core_id; i < M * P; i += num_cores) {
      float error = 0.0f;
      float exp = C[i];
      float res = Exp[i];
      asm volatile("fsub.s %[error], %[res], %[exp];"
                   : [error] "+&r"(error)
                   : [res] "r"(res), [exp] "r"(exp));
      if ((int32_t)error != 0) {
        printf("ERROR!!! %d\n", i);
      }
    }
  }

  // Wait at barrier before checking
  mempool_barrier(num_cores);

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
  matmul_2x2_parallel_f32_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
                                matrix_N, matrix_P, core_id, num_cores);
  mempool_stop_benchmark();
  // Wait at barrier before checking
  mempool_barrier(num_cores);
#elif defined(SINGLE)
  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    matmul_2x2_single_f32_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
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
