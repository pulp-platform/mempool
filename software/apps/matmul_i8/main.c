// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "mempool_matmul_i8p.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#define matrix_M 64
#define matrix_N 64
#define matrix_P 64

int8_t matrix_a[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
int8_t matrix_b[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

int volatile error __attribute__((section(".l1")));

void init_matrix(int8_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int8_t a, int8_t b, int8_t c, uint32_t core_id,
                 uint32_t num_cores) {
  uint32_t const split = 8; // How many rows/columns to split the matrix into
  if (num_columns > num_rows) {
    // Parallelize over columns
    uint32_t const c_start = (num_rows / split) * (core_id % split);
    uint32_t const c_end = (num_rows / split) * ((core_id % split) + 1);
    for (uint32_t j = (core_id / split); j < num_columns;
         j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        matrix[i * num_columns + j] =
            (int8_t)(a * (int8_t)i + b * (int8_t)j + c);
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (num_columns / split) * (core_id % split);
    uint32_t const c_end = (num_columns / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < num_rows;
         i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        matrix[i * num_columns + j] =
            (int8_t)(a * (int8_t)i + b * (int8_t)j + c);
      }
    }
  }
}

// Initialize the matrices in parallel
int verify_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                  uint32_t inner_dim, int8_t aa, int8_t ab, int8_t ac,
                  int8_t ba, int8_t bb, int8_t bc, uint32_t core_id,
                  uint32_t num_cores) {
  // Convert to signed
  int32_t n = (int32_t)inner_dim;
  // Parallelize over rows
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      int32_t ii = (int32_t)i;
      int32_t jj = (int32_t)j;
      int32_t lin = ((int32_t)aa * bb * ii * jj + aa * bc * ii + ac * bb * jj +
                     (int32_t)ac * bc) *
                    n;
      int32_t qua =
          (((int32_t)aa * ba * ii + ab * bb * jj + ab * bc + (int32_t)ba * ac) *
           (n * (n - 1))) /
          2;
      int32_t cub = (((int32_t)ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;
      int32_t golden = lin + qua + cub;
      if (matrix[i * num_columns + j] != golden) {
        return (i + j) == 0 ? -1 : (int)(i * num_columns + j);
      }
      matrix[i * num_columns + j] = 0;
    }
  }
  return 0;
}

int test_matrix_multiplication(int8_t *__restrict__ A, int8_t *__restrict__ B,
                               int32_t *__restrict__ C, uint32_t M, uint32_t N,
                               uint32_t P, uint32_t core_id,
                               uint32_t num_cores) {
  int8_t const A_a = 1;
  int8_t const A_b = 1;
  int8_t const A_c = -40;
  int8_t const B_a = 0;
  int8_t const B_b = 1;
  int8_t const B_c = 19;

  // Initialize Matrices
  init_matrix(A, M, N, A_a, A_b, A_c, core_id, num_cores);
  init_matrix(B, N, P, B_a, B_b, B_c, core_id, num_cores);
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  // Execute function to test.
  mempool_start_benchmark();

#ifdef __XPULPIMG
  matmul_unrolled_2x4_pincr_asm_parallel_i8_xpulpv2(A, B, C, M, N, P, core_id,
                                                    num_cores);
  // matmul_unrolled_2x4_parallel_i8_xpulpv2(A, B, C, M, N, P, core_id,
  // num_cores);
#else
  matmul_unrolled_2x2_parallel_i8_rv32im(A, B, C, M, N, P, core_id, num_cores);
#endif

  mempool_stop_benchmark();
  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  if (verify_matrix(C, M, P, N, A_a, A_b, A_c, B_a, B_b, B_c, core_id,
                    num_cores)) {
    error = 1;
    return -1;
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

  // Test the Matrix multiplication
  test_matrix_multiplication(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                             matrix_P, core_id, num_cores);
  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
