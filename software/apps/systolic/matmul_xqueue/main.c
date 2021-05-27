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
#include "systolic/matmul_xqueue.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Dimensions of matrices
#define DIM_M 16
#define DIM_N 16
#define DIM_P 16

uint32_t *grid_mapping;

int32_t *matrix_A;
int32_t *matrix_B;

uint32_t rep_count;

systolic_matrix_t *syst_matrix_A;
systolic_matrix_t *syst_matrix_B;
systolic_matrix_t *syst_matrix_C;

void generate_gradient_matrix(int32_t **matrix, uint32_t num_rows,
                              uint32_t num_cols) {
  int32_t *new_matrix = (int32_t *)simple_malloc(num_rows * num_cols * 4);
  for (uint32_t y = 0; y < num_rows; ++y) {
    for (uint32_t x = 0; x < num_cols; ++x) {
      new_matrix[y * num_cols + x] = (int32_t)(y + x);
    }
  }
  *matrix = new_matrix;
}

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
  uint32_t tile_id = core_id / 4;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id, num_cores);

  // Allocate systolic grid mapping
  if (core_id == 0) {
    grid_mapping = (uint32_t *)simple_malloc(num_cores * 4);
  }

  // ----------
  // 16 CORES
  // ----------

  // Assign grid position (row wise)
  // uint32_t col_idx = core_id % 4;
  // uint32_t row_idx = core_id / 4;

  // Assign grid position (col wise)
  uint32_t col_idx = core_id / 4;
  uint32_t row_idx = core_id % 4;

  // Assign grid position (tile wise)
  // uint32_t col_idx;
  // uint32_t row_idx;
  // if (core_id < 4) {
  //   col_idx = core_id % 2;
  //   row_idx = core_id / 2;
  // } else if (core_id < 8) {
  //   col_idx = core_id % 2 + 2;
  //   row_idx = core_id / 6;
  // } else if (core_id < 12) {
  //   col_idx = core_id % 2;
  //   row_idx = core_id / 10 + 2;
  // } else {
  //   col_idx = core_id % 2 + 2;
  //   row_idx = core_id / 14 + 2;
  // }

  // uint32_t mapped_tile = tile_id;

  // ----------
  // 256 CORES
  // ----------

  // Assign grid position (col wise)
  // uint32_t col_idx = core_id / 16;
  // uint32_t row_idx = core_id % 16;

  // Assign grid position (tile wise)
  // uint32_t mapped_group = core_id % 4;
  // uint32_t col_idx = tile_id / 4;
  // uint32_t row_idx = (tile_id % 4) + (mapped_group * 4);
  // uint32_t mapped_tile = (tile_id % 16) + (mapped_group * 16);

  // Wait for all cores
  mempool_barrier(num_cores);

  // Set systolic grid mapping
  grid_mapping[row_idx * SYSTOLIC_SIZE + col_idx] = tile_id;

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out grid mapping
    // print_matrix((int32_t *)grid_mapping, 4, 4);

    // Initialize systolic array
    systolic_init(grid_mapping);

    // Create systolic matrices
    generate_gradient_matrix(&matrix_A, DIM_M, DIM_N);
    systolic_matrix_create(&syst_matrix_A, matrix_A, DIM_M, DIM_N);
    simple_free(matrix_A);
    generate_gradient_matrix(&matrix_B, DIM_N, DIM_P);
    systolic_matrix_create(&syst_matrix_B, matrix_B, DIM_N, DIM_P);
    simple_free(matrix_B);
    systolic_matrix_allocate(&syst_matrix_C, DIM_M, DIM_P);

    // Print out systolic matrices A & B
    // printf("> Print Systolic Matrices A & B\n");
    // systolic_matrix_print(syst_matrix_A);
    // systolic_matrix_print(syst_matrix_B);

    // Set repetition count per submatrix of C (A->num_cols == B->num_rows)
    rep_count = syst_matrix_A->num_cols / 2;
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Start benchmark
    printf("> Start\n");
    mempool_start_benchmark();
  }

  // Start benchmark for all cores
  // mempool_barrier(num_cores);
  // mempool_start_benchmark();

  // Wait for all cores
  mempool_barrier(num_cores);

  if ((row_idx == 0) && (col_idx == 0)) {
    systolic_rcp_pe(rep_count, syst_matrix_A, syst_matrix_B, syst_matrix_C);
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    systolic_cp_pe(col_idx, rep_count, syst_matrix_B, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    systolic_rp_pe(row_idx, rep_count, syst_matrix_A, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    systolic_np_pe(row_idx, col_idx, rep_count, syst_matrix_C);
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Stop benchmark for all cores
  // mempool_stop_benchmark();
  // mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    // Stop benchmark
    mempool_stop_benchmark();
    printf("> End\n");

    // Print out systolic matrix C
    // printf("> Print Systolic Matrix C\n");
    // systolic_matrix_print(syst_matrix_C);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
