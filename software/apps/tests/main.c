// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/mat_mul.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#if NUM_CORES > 32
#define matrix_M 256
#define matrix_N 256
#define matrix_P 256
#else
#define matrix_M (NUM_CORES)
#define matrix_N (NUM_CORES)
#define matrix_P (NUM_CORES)
#endif

int32_t matrix_a[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
int32_t matrix_b[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

int volatile error __attribute__((section(".l2")));

dump(time, 0);

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  uint32_t const split = 8; // How many rows/columns to split the matrix into
  if (num_columns > num_rows) {
    // Parallelize over columns
    uint32_t const c_start = (num_rows / split) * (core_id % split);
    uint32_t const c_end = (num_rows / split) * ((core_id % split) + 1);
    for (uint32_t j = (core_id / split); j < num_columns;
         j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (num_columns / split) * (core_id % split);
    uint32_t const c_end = (num_columns / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < num_rows;
         i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  }
}

// Initialize the matrices in parallel
int verify_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                  uint32_t inner_dim, int32_t aa, int32_t ab, int32_t ac,
                  int32_t ba, int32_t bb, int32_t bc, uint32_t core_id,
                  uint32_t num_cores) {
  // Convert to signed
  int32_t n = (int32_t)inner_dim;
  // Parallelize over tiles
  uint32_t const c = 16; // How many columns to split the matrix into
  uint32_t const c_start = (num_columns / c) * (core_id % c);
  uint32_t const c_end = (num_columns / c) * ((core_id % c) + 1);
  for (uint32_t i = core_id / c; i < num_rows; i += num_cores / c) {
    for (uint32_t j = c_start; j < c_end; j++) {
      int32_t ii = (int32_t)i;
      int32_t jj = (int32_t)j;
      int32_t lin =
          (aa * bb * ii * jj + aa * bc * ii + ac * bb * jj + ac * bc) * n;
      int32_t qua =
          ((aa * ba * ii + ab * bb * jj + ab * bc + ba * ac) * (n * (n - 1))) /
          2;
      int32_t cub = ((ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;
      int32_t golden = lin + qua + cub;
      // printf("C %3d %3d 0x%08x\n", i, j, (uint32_t)&matrix[i * num_columns +
      // j]);
      if (matrix[i * num_columns + j] != golden) {
        return (i + j) == 0 ? -1 : (int)(i * num_columns + j);
      }
      matrix[i * num_columns + j] = 0;
    }
  }
  return 0;
}

int test_matrix_multiplication(int32_t *__restrict__ A, int32_t *__restrict__ B,
                               int32_t *__restrict__ C, uint32_t M, uint32_t N,
                               uint32_t P, uint32_t core_id,
                               uint32_t num_cores) {
  int32_t const A_a = 1;
  int32_t const A_b = 1;
  int32_t const A_c = -32;
  int32_t const B_a = 2;
  int32_t const B_b = 1;
  int32_t const B_c = 16;

  // Initialize Matrices
  init_matrix(A, M, N, A_a, A_b, A_c, core_id, num_cores);
  init_matrix(B, N, P, B_a, B_b, B_c, core_id, num_cores);
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

  // Cold cache
  uint32_t start = mempool_get_timer();
  mempool_start_benchmark();
  mat_mul_unrolled_4x4_parallel_asm(A, B, C, M, N, P, core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  uint32_t stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

  // Hot cache
  mempool_barrier(num_cores);
  start = mempool_get_timer();
  mempool_start_benchmark();
  mat_mul_unrolled_4x4_parallel_asm(A, B, C, M, N, P, core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

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
