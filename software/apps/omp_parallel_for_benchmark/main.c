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
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#define M 32
#define N 32
#define P 32
// Specify how the matrices A and B should be initialized
// The entries will follow this format:
// a(i,j) = A_a*i + A_b*j + A_c
// b(i,j) = B_a*i + B_b*j + B_c
// The result will be the following matrix
// c(i,j) = (A_a*B_b*i*j + A_a*B_c*i + A_c*B_b*j + A_c*B_c) * N
//        + (A_a*B_a*i + A_b*B_b*j + A_b*B_c + B_a*A_c) * (N*(N-1))/2
//        + (A_b*B_a) * (N*(N-1)*(2*N-1))/6
// Note: To keep the code simpler, we use indices that go from 0 to N-1 instead
// of 1 to N as the mathematicians do. Hence, for A, i=[0,M-1] j=[0,M-1]
#define A_a 1
#define A_b 1
#define A_c -32
#define B_a 2
#define B_b 1
#define B_c 16

int32_t volatile init __attribute__((section(".l2"))) = 0;
int32_t a[M * N] __attribute__((section(".l1")));
int32_t b[N * P] __attribute__((section(".l1")));
int32_t c[M * P] __attribute__((section(".l1")));

// Initialize the matrices in parallel
void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  // Parallelize over rows
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
    }
  }
}

// Initialize the matrices in parallel
int verify_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                  int32_t aa, int32_t ab, int32_t ac, int32_t ba, int32_t bb,
                  int32_t bc) {
  // Parallelize over rows
  for (int32_t i = 0; i < (int32_t)num_rows; ++i) {
    for (int32_t j = 0; j < (int32_t)num_columns; ++j) {
      int32_t lin = (aa * bb * i * j + aa * bc * i + ac * bb * j + ac * bc) * N;
      int32_t qua =
          ((aa * ba * i + ab * bb * j + ab * bc + ba * ac) * (N * (N - 1))) / 2;
      int32_t cub = ((ab * ba) * (N * (N - 1) * (2 * N - 1))) / 6;
      int32_t golden = lin + qua + cub;
      if (matrix[i * (int32_t)num_columns + j] != golden) {
        return (i + j) == 0 ? -1 : i * (int32_t)num_columns + j;
      }
      matrix[i * (int32_t)num_columns + j] = 0;
    }
  }
  return 0;
}

void print_matrix(int32_t const *matrix, uint32_t num_rows,
                  uint32_t num_columns) {
  printf("0x%8X\n", (uint32_t)matrix);
  for (uint32_t i = 0; i < num_rows; ++i) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      printf("%5d ", matrix[i * num_columns + j]);
    }
    printf("\n");
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_timer_t cycles;
  int error;

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // Initialize Matrices
  init_matrix(a, M, N, A_a, A_b, A_c, core_id, num_cores);
  init_matrix(b, N, P, B_a, B_b, B_c, core_id, num_cores);

  mempool_barrier(num_cores, num_cores / 2);

  cycles = mempool_get_timer();
  mempool_start_benchmark();
  mat_mul_parallel(a, b, c, M, N, P, core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  mempool_barrier(num_cores, num_cores * 4);

  // Check result
  if (core_id == 0) {
    printf("Manual Parallel Duration: %d\n", cycles);
    error = verify_matrix(c, M, P, A_a, A_b, A_c, B_a, B_b, B_c);
    if (error != 0) {
      printf("Error code %d\n", error);
      printf("c[%d]=%d\n", error, c[error]);
    }
  } else {
    mempool_wait(M * P * 12);
  }
  mempool_barrier(num_cores, num_cores * 4);

  cycles = mempool_get_timer();
  mempool_start_benchmark();
  mat_mul_unrolled_parallel(a, b, c, M, N, P, core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  mempool_barrier(num_cores, num_cores * 4);

  // Check result
  if (core_id == 0) {
    printf("Manual unrolled Parallel Duration: %d\n", cycles);
    error = verify_matrix(c, M, P, A_a, A_b, A_c, B_a, B_b, B_c);
    if (error != 0) {
      printf("Error code %d\n", error);
      printf("c[%d]=%d\n", error, c[error]);
    }
  } else {
    mempool_wait(M * P * 12);
  }
  mempool_barrier(num_cores, num_cores * 4);

  if (core_id == 0) {

    mempool_wait(1000);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    mat_mul_sequential(a, b, c, M, N, P);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("Sequqntial Duration: %d\n", cycles);
    error = verify_matrix(c, M, P, A_a, A_b, A_c, B_a, B_b, B_c);
    if (error != 0) {
      printf("Error code %d\n", error);
      printf("c[%d]=%d\n", error, c[error]);
    }

    printf("Start openMP\n");

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    mat_mul_parallel_omp(a, b, c, M, N, P);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("OpenMP Parallel Duration: %d\n", cycles);
    error = verify_matrix(c, M, P, A_a, A_b, A_c, B_a, B_b, B_c);
    if (error != 0) {
      printf("Error code %d\n", error);
      printf("c[%d]=%d\n", error, c[error]);
    }

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    mat_mul_unrolled_parallel_omp(a, b, c, M, N, P);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
    printf("OpenMP Unrolled Parallel Duration: %d\n", cycles);
    error = verify_matrix(c, M, P, A_a, A_b, A_c, B_a, B_b, B_c);
    if (error != 0) {
      printf("Error code %d\n", error);
      printf("c[%d]=%d\n", error, c[error]);
    }

  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
