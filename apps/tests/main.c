// Copyright 2020 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/mat_mul.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

uint32_t volatile error __attribute__((section(".l1")));

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#ifdef NUM_CORES
#define matrix_M NUM_CORES
#define matrix_N 8
#define matrix_P NUM_CORES
#else
#define matrix_M 256
#define matrix_N 16
#define matrix_P 256
#endif
int32_t matrix_a[matrix_M * matrix_N] __attribute__((section(".l1")));
int32_t matrix_b[matrix_N * matrix_P] __attribute__((section(".l1")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1")));

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  if (num_columns > num_rows) {
    // Parallelize over columns
    for (int j = core_id; j < num_columns; j += num_cores) {
      for (int i = 0; i < num_rows; ++i) {
        matrix[i * num_columns + j] = a * i + b * j + c;
      }
    }
  } else {
    // Parallelize over rows
    for (int i = core_id; i < num_rows; i += num_cores) {
      for (int j = 0; j < num_columns; ++j) {
        matrix[i * num_columns + j] = a * i + b * j + c;
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
  // Parallelize over rows
  for (int32_t i = core_id; i < num_rows; i += num_cores) {
    for (int32_t j = 0; j < num_columns; ++j) {
      int32_t lin = (aa * bb * i * j + aa * bc * i + ac * bb * j + ac * bc) * n;
      int32_t qua =
          ((aa * ba * i + ab * bb * j + ab * bc + ba * ac) * (n * (n - 1))) / 2;
      int32_t cub = ((ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;
      int32_t golden = lin + qua + cub;
      if (matrix[i * num_columns + j] != golden) {
        return (i + j) == 0 ? -1 : i * num_columns + j;
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
  mempool_barrier(core_id, num_cores, num_cores / 2);
  // Execute function to test.
  mempool_start_benchmark();
  mat_mul_asm_parallel(A, B, C, M, N, P, core_id, num_cores);
  mempool_stop_benchmark();
  // Wait at barrier befor checking
  mempool_barrier(core_id, num_cores, num_cores * 4);
  if (verify_matrix(C, M, P, N, A_a, A_b, A_c, B_a, B_b, B_c, core_id,
                    num_cores)) {
    error = 1;
    return -1;
  }
  return 0;
}

int main(int argc, char **argv) {
  uint32_t core_id = (uint32_t)argc;
  uint32_t num_cores = (uint32_t)argv;
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    error = 0;
  }

  // Test the Matrix multiplication
  test_matrix_multiplication(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                             matrix_P, core_id, num_cores);
  // wait until all cores have finished
  mempool_barrier(core_id, num_cores, num_cores * 4);

  return error;
}
