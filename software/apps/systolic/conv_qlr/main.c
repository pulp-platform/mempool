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
#include "systolic/conv_qlr.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Dimensions of matrices X and Y
#define DIM_M 256
#define DIM_N 61

// Repetition count
#define REP_COUNT 5

// Systolic Length (must be divisor of NUM_CORES)
#define SYSTOLIC_LENGTH 128

uint32_t *core_map;

int32_t *matrix_X;
int32_t *matrix_Y;

const int32_t weights[3][3] = {{1, 1, 1}, {1, 1, 1}, {1, 1, 1}};
int32_t *matrix_W[NUM_CORES / 4];

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

void fill_gradient_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_cols,
                          uint32_t core_id, uint32_t num_cores) {
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
  mempool_barrier_init(core_id, num_cores);

  // Initialization
  mempool_init(core_id, num_cores);

  // Allocate tile and core maps
  if (core_id == 0) {
    core_map = (uint32_t *)simple_malloc(num_cores * 4);
  }

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Set tile and core maps
  core_map[core_id] = core_id;

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Setup: Systolic initialization and matrix_X
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out map
    // print_matrix((int32_t *)core_map, 1, num_cores);

    // Initialize systolic array
    systolic_init(core_map);

    // Create and initialize matrices
    matrix_X = (int32_t *)simple_malloc(DIM_M * DIM_N * 4);
    matrix_Y = (int32_t *)simple_malloc(DIM_M * DIM_N * 4);
  }

  // Setup: Distribute weights
  if (core_id % 4 == 1) {
    // Get tile allocator
    alloc_t *tile_alloc = get_alloc_tile(tile_id);

    // Allocate local matrix_W
    matrix_W[tile_id] = (int32_t *)domain_malloc(tile_alloc, 9 * 4);

    // Load weights
    for (uint32_t y = 0; y < 3; ++y) {
      for (uint32_t x = 0; x < 3; ++x) {
        (matrix_W[tile_id])[y * 3 + x] = weights[y][x];
      }
    }
  }

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Fill matrix with gradient
  fill_gradient_matrix(matrix_X, DIM_M, DIM_N, core_id, num_cores);

  if (core_id == 0) {
    // Print out matrix X
    // printf("> Print Matrix X\n");
    // print_matrix(matrix_X, DIM_M, DIM_N);

    printf("> Start\n");
  }

  // Start benchmark for all cores
  mempool_sleep_barrier(num_cores);
  mempool_start_benchmark();

  switch (core_id % SYSTOLIC_LENGTH) {
  case 0:
    systolic_conv_front(core_id, num_cores, DIM_M, DIM_N, matrix_X,
                        matrix_W[tile_id], matrix_Y, REP_COUNT);
    break;
  case (SYSTOLIC_LENGTH - 1):
    systolic_conv_end(core_id, num_cores, DIM_M, DIM_N, matrix_X,
                      matrix_W[tile_id], matrix_Y, REP_COUNT);
    break;
  default:
    systolic_conv_mid(core_id, num_cores, DIM_M, DIM_N, matrix_X,
                      matrix_W[tile_id], matrix_Y, REP_COUNT);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_sleep_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    printf("> End\n");

    // Print out matrix Y
    // printf("> Print Matrix Y\n");
    // print_matrix(matrix_Y, DIM_M, DIM_N);
  }

  // wait until all cores have finished
  mempool_sleep_barrier(num_cores);
  return 0;
}
