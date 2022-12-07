// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "systolic/conv_xqueue.h"

// Dimensions of matrix X
#define DIM_X_M 258
#define DIM_X_N 61

// Dimensions of matrix Y
#define DIM_Y_M (DIM_X_M - 2)
#define DIM_Y_N (DIM_X_N - 2)

uint32_t *tile_map;
uint32_t *core_map;

int32_t *matrix_X;
int32_t *matrix_Y;

int32_t weights[3][3] = {{1, 1, 1}, {1, 1, 1}, {1, 1, 1}};
int32_t *matrix_W = (int32_t *)weights;

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
  uint32_t tile_id = core_id / NUM_CORES_PER_TILE;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id);

  // Allocate tile and core maps
  if (core_id == 0) {
    tile_map = (uint32_t *)simple_malloc(num_cores * sizeof(uint32_t));
    core_map = (uint32_t *)simple_malloc(num_cores * sizeof(uint32_t));
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Set tile and core maps
  tile_map[core_id] = tile_id;
  core_map[core_id] = core_id;

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out maps
    // print_matrix((int32_t *)tile_map, 1, num_cores);
    // print_matrix((int32_t *)core_map, 1, num_cores);

    // Initialize systolic array
    systolic_init(tile_map, core_map);

    // Create and initialize matrices
    generate_gradient_matrix(&matrix_X, DIM_X_M, DIM_X_N);
    matrix_Y = (int32_t *)simple_malloc(DIM_Y_M * DIM_Y_N * sizeof(int32_t));

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

  switch (core_id) {
  case 0:
    systolic_conv_front(DIM_X_M, DIM_X_N, matrix_X, matrix_W, matrix_Y);
    break;
  case (NUM_CORES - 1):
    systolic_conv_end(core_id, DIM_X_M, DIM_X_N, matrix_X, matrix_W, matrix_Y);
    break;
  default:
    systolic_conv_mid(core_id, DIM_X_M, DIM_X_N, matrix_X, matrix_W, matrix_Y);
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
    // printf("> Print Matrix Y\n");
    // print_matrix(matrix_Y, DIM_Y_M, DIM_Y_N);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
