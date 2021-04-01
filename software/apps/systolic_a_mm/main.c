// Copyright 2021 ETH Zurich and University of Bologna.
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

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "kernel/queue.h"
#include "kernel/systolic_a.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define DIM_M 3
#define DIM_N 3
#define DIM_P 3

extern int32_t __heap_start, __heap_end;

int32_t A[DIM_M][DIM_N] = {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}};
int32_t B[DIM_N][DIM_P] = {{0, 1, 2}, {3, 4, 5}, {6, 7, 8}};

int32_t *matrix_A = (int32_t *)A;
int32_t *matrix_B = (int32_t *)B;

systolic_matrix_t *syst_matrix_A;
systolic_matrix_t *syst_matrix_B;
systolic_matrix_t *syst_matrix_C;

void print_matrix(int32_t const *matrix, uint32_t num_rows,
                  uint32_t num_columns) {
  printf("Matrix at 0x%8X\n", (uint32_t)matrix);
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

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize Allocator\n");

    // Initialize malloc
    uint32_t heap_size = (uint32_t)(&__heap_end - &__heap_start);
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);

    // Initialize systolic array
    printf("> Initialize Systolic Architecture\n");
    systolic_init();

    // Create systolic matrices
    printf("> Allocate Systolic Matrices\n");
    systolic_matrix_create(&syst_matrix_A, matrix_A, DIM_M, DIM_N);
    systolic_matrix_create(&syst_matrix_B, matrix_B, DIM_N, DIM_P);
    systolic_matrix_allocate(&syst_matrix_C, DIM_M, DIM_P);

    // Print out systolic matrices A & B
    printf("> Print Systolic Matrices A & B\n");
    systolic_matrix_print(syst_matrix_A);
    systolic_matrix_print(syst_matrix_B);
  }

  // Wait for all cores
  mempool_barrier(num_cores, num_cores * 4);

  // Assign grid position
  uint32_t col_idx = core_id % 4;
  uint32_t row_idx = core_id / 4;

  if ((row_idx == 0) && (col_idx == 0)) {
    // Instruct systolic matrix multiplication
    systolic_matrix_mul(syst_matrix_A, syst_matrix_B, syst_matrix_C);

    // Print out systolic matrix C
    printf("> Print Systolic Matrix C\n");
    systolic_matrix_print(syst_matrix_C);

    // Kill systolic loop
    printf("> Kill Systolic Loop\n");
    systolic_kill_loop();
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    systolic_column_ctrl(col_idx);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    systolic_row_ctrl(row_idx);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    systolic_proc_element(row_idx, col_idx);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);
  return 0;
}
