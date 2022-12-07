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
#include "systolic/matmul_qlr.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Dimensions of matrices
#define DIM_M 96 // TODO: ASSERT DIVISABLE BY 3
#define DIM_N 96
#define DIM_P 96 // TODO: ASSERT DIVISABLE BY 3

uint32_t *core_map;

int32_t *matrix_A;
int32_t *matrix_B;
int32_t *matrix_C;

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

void fill_gradient_matrix(int32_t *matrix, uint32_t num_rows,
                          uint32_t num_cols, uint32_t core_id,
                          uint32_t num_cores) {
  for (uint32_t y = core_id; y < num_rows; y += num_cores) {
    for (uint32_t x = 0; x < num_cols; ++x) {
      matrix[y * num_cols + x] = (int32_t)(y + x);
    }
  }
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
    core_map = (uint32_t *)simple_malloc(num_cores * sizeof(uint32_t));
  }

#if NUM_CORES == 16
  // ----------
  // 16 CORES
  // ----------

  // Assign grid position (row wise)
  // uint32_t col_idx = core_id % 4;
  // uint32_t row_idx = core_id / 4;

  // Assign grid position (col wise)
  // uint32_t col_idx = core_id / 4;
  // uint32_t row_idx = core_id % 4;

  // Assign grid position (square wise)
  uint32_t col_idx = tile_id % 2;
  col_idx *= 2;
  col_idx += core_id % 2;
  uint32_t row_idx = tile_id / 2;
  row_idx *= 2;
  row_idx += (core_id % 4) / 2;

#elif NUM_CORES == 256
  // ----------
  // 256 CORES
  // ----------
  // Assign grid position (row wise)
  // uint32_t col_idx = core_id % 16;
  // uint32_t row_idx = core_id / 16;

  // Assign grid position (col wise)
  uint32_t col_idx = core_id / 16;
  uint32_t row_idx = core_id % 16;

  // Assign grid position (square wise)
  uint32_t col_idx = tile_id % 8;
  col_idx *= 2;
  col_idx += core_id % 2;
  uint32_t row_idx = tile_id / 8;
  row_idx *= 2;
  row_idx += (core_id % 4) / 2;

  // Assign grid position (square square wise)
  // uint32_t group_id = tile_id / 16;
  // uint32_t add_col = group_id % 2;
  // uint32_t add_row = group_id / 2;
  // uint32_t col_idx = tile_id % 4;
  // col_idx *= 2;
  // col_idx += core_id % 2;
  // col_idx += add_col * 8;
  // uint32_t row_idx = (tile_id % 16) / 4;
  // row_idx *= 2;
  // row_idx += (core_id % 4) / 2;
  // row_idx += add_row * 8;
#else
#error Unsupported NUM_CORES
#endif

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Set tile and core mapping
  core_map[row_idx * SYSTOLIC_SIZE + col_idx] = core_id;

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out core mapping
    // print_matrix((int32_t *)core_map, SYSTOLIC_SIZE, SYSTOLIC_SIZE);

    // Initialize systolic array
    systolic_init(core_map);

    // Create matrices
    matrix_A = (int32_t *)simple_malloc(DIM_M * DIM_N * 4);
    matrix_B = (int32_t *)simple_malloc(DIM_N * DIM_P * 4);
    matrix_C = (int32_t *)simple_malloc(DIM_M * DIM_P * 4);
  }

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Fill matrices with gradient
  fill_gradient_matrix(matrix_A, DIM_M, DIM_N, core_id, num_cores);
  fill_gradient_matrix(matrix_B, DIM_N, DIM_P, core_id, num_cores);

  // Start message
  if (core_id == 0) {
    // Print out matrices A & B
    // printf("> Print Matrices A & B\n");
    // print_matrix(matrix_A, DIM_M, DIM_N);
    // print_matrix(matrix_B, DIM_N, DIM_P);

    printf("> Start\n");
  }

  // Start benchmark for all cores
  mempool_sleep_barrier(num_cores);
  mempool_start_benchmark();

  if ((row_idx == 0) && (col_idx == 0)) {
    systolic_rcp_pe(num_cores, DIM_M, DIM_N, DIM_P, matrix_A, matrix_B,
                    matrix_C);
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    systolic_cp_pe(num_cores, col_idx, DIM_M, DIM_N, DIM_P, matrix_B, matrix_C);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    systolic_rp_pe(num_cores, row_idx, DIM_M, DIM_N, DIM_P, matrix_A, matrix_C);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    systolic_np_pe(num_cores, row_idx, col_idx, DIM_M, DIM_N, DIM_P, matrix_C);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_sleep_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    printf("> End\n");

    // Print out matrix C
    // printf("> Print Matrix C\n");
    // print_matrix(matrix_C, DIM_M, DIM_P);
  }

  // wait until all cores have finished
  mempool_sleep_barrier(num_cores);
  return 0;
}
