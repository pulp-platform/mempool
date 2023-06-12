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

typedef __fp16 v2f16 __attribute__((vector_size(4)));
typedef union {
  float f32;
  v2f16 vec;
} v2h;

#include "data_matmulf32.h"
#include "kernel/mat_mul_f32.h"

#define PARALLEL
#define ASM

float matrix_a[matrix_M * matrix_N] __attribute__((section(".l1")));
float matrix_b[matrix_N * matrix_P] __attribute__((section(".l1")));
float matrix_c[matrix_M * matrix_P] __attribute__((section(".l1")));

int volatile error __attribute__((section(".l1")));

void init_matrix(float *matrix, float *input, uint32_t num_rows,
                 uint32_t num_columns, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < (num_columns * num_rows); i += num_cores) {
    matrix[i] = input[i];
  }
}

int verify_result(float *__restrict__ C, float *__restrict__ Exp, uint32_t M,
                  uint32_t P, uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < M * P; i++) {
      float error = 0.0f;
      float exp = Exp[i];
      float res = C[i];
      asm volatile("fsub.s %[error], %[res], %[exp];"
                   : [error] "+&r"(error)
                   : [res] "r"(res), [exp] "r"(exp));
      if (error != 0.0f) {
        printf("ERROR!!! OUT[%d] = 0x%8x\n", i, *(uint32_t *)&error);
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
  // matmul_2x2_parallel_f32_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
  //                               matrix_N, matrix_P, core_id, num_cores);
  matmul_4x4_parallel_f32_zfinx(matrix_a, matrix_b, matrix_c, matrix_M,
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
