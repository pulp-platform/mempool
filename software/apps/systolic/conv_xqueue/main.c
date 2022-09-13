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
#include "systolic/conv_xqueue.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Dimensions of matrix X
#define DIM_X_M 32
#define DIM_X_N 32

// Dimensions of matrix Y
#define DIM_Y_M (DIM_X_M - (KERNEL_SIZE - 1))
#define DIM_Y_N (DIM_X_N - (KERNEL_SIZE - 1))

// Dimensions of maps
#define KERNEL_ROWS KERNEL_SIZE
#define KERNEL_COLS KERNEL_SIZE *NUM_KERNELS
#define NUM_ACCS NUM_KERNELS

uint32_t *kernel_tile_map;
uint32_t *kernel_core_map;
uint32_t *row_acc_tile_map;
uint32_t *row_acc_core_map;

int32_t *matrix_X;
int32_t *matrix_Y;

int32_t weights[3][3] = {{1, 1, 1}, {1, 1, 1}, {1, 1, 1}};

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

  // Allocate tile and core maps
  if (core_id == 0) {
    kernel_tile_map = (uint32_t *)simple_malloc(KERNEL_ROWS * KERNEL_COLS * 4);
    kernel_core_map = (uint32_t *)simple_malloc(KERNEL_ROWS * KERNEL_COLS * 4);
    row_acc_tile_map = (uint32_t *)simple_malloc(NUM_ACCS * 4);
    row_acc_core_map = (uint32_t *)simple_malloc(NUM_ACCS * 4);
  }

  // Systolic identifiers
  int32_t is_enabled = 0;
  int32_t is_kernel_core = 0;
  uint32_t kernel_id = 0;
  uint32_t kernel_row = 0;
  uint32_t kernel_col = 0;

  // ----------
  // ACC COMBO
  // ----------

  // TODO: VISUAL DESCRIPTION
  // TODO: CURRENTLY ONLY WORKS FOR KERNEL_SIZE == 3

  kernel_id = tile_id / 5;
  uint32_t kernel_pair_id = tile_id % 5;
  uint32_t tile_core_id = core_id % 4;
  if (kernel_pair_id < 3) {
    is_kernel_core = 1;
    kernel_row = kernel_pair_id;
    kernel_col = tile_core_id % 2;
    kernel_id += tile_core_id / 2;
  } else {
    if (tile_core_id == 3) {
      is_kernel_core = 0;
    } else {
      is_kernel_core = 1;
      kernel_row = tile_core_id;
      kernel_col = 2;
    }
    kernel_id += kernel_pair_id % 3;
  }

  // Core is only enabled if its kernel is required
  if (kernel_id < NUM_KERNELS) {
    is_enabled = 1;
  } else {
    is_enabled = 0;
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Set tile and core maps
  if (is_enabled) {
    if (is_kernel_core) {
      kernel_tile_map[kernel_row * KERNEL_COLS + kernel_col] = tile_id;
      kernel_core_map[kernel_row * KERNEL_COLS + kernel_col] = core_id;
    } else {
      row_acc_tile_map[kernel_id] = tile_id;
      row_acc_core_map[kernel_id] = core_id;
    }
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out maps
    // print_matrix((int32_t *)kernel_tile_map, KERNEL_ROWS, KERNEL_COLS);
    // print_matrix((int32_t *)kernel_core_map, KERNEL_ROWS, KERNEL_COLS);
    // print_matrix((int32_t *)row_acc_tile_map, 1, NUM_ACCS);
    // print_matrix((int32_t *)row_acc_core_map, 1, NUM_ACCS);

    // Initialize systolic array
    systolic_init(kernel_tile_map, kernel_core_map, row_acc_tile_map,
                  row_acc_core_map);

    // Create and initialize matrices
    generate_gradient_matrix(&matrix_X, DIM_X_M, DIM_X_N);
    matrix_Y = (int32_t *)simple_malloc(DIM_Y_M * DIM_Y_N * 4);

    // Print out matrix X
    // printf("> Print Matrix X\n");
    // print_matrix(matrix_X, DIM_X_M, DIM_X_N);
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Start benchmark
    printf("> Start\n");
    // mempool_start_benchmark();
  }

  // Start benchmark for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Wait for all cores
  mempool_barrier(num_cores);

  if (is_enabled) {
    if (is_kernel_core) {
      switch (kernel_col) {
      case 0:
        if (kernel_id == 0) {
          systolic_conv_first_leader(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                                     matrix_X, (int32_t *)weights);
        } else {
          if (kernel_row == 2) {
            systolic_conv_first_leader(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                                       matrix_X, (int32_t *)weights);
          } else {
            systolic_conv_leader(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                                 (int32_t *)weights);
          }
        }
        break;
      case (KERNEL_SIZE - 1):
        if (kernel_id == NUM_KERNELS - 1) {
          systolic_conv_last_NAME(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                                  (int32_t *)weights);
        } else {
          if (kernel_row == 0) {
            systolic_conv_last_NAME(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                                    (int32_t *)weights);
          } else {
            systolic_conv_NAME(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                               (int32_t *)weights);
          }
        }
        break;
      default:
        systolic_conv_follower(kernel_id, kernel_row, DIM_X_M, DIM_X_N,
                               (int32_t *)weights);
      }
    } else {
      systolic_conv_row_acc(kernel_id, DIM_Y_M, DIM_Y_N, matrix_Y);
    }
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    // Stop benchmark
    // mempool_stop_benchmark();
    printf("> End\n");

    // Print out matrix Y
    printf("> Print Matrix Y\n");
    print_matrix(matrix_Y, DIM_Y_M, DIM_Y_N);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
