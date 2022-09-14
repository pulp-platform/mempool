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
#include "systolic/matmul.h"

// Dimensions of matrices
#define DIM_M 32
#define DIM_N 32
#define DIM_P 32

uint32_t *grid_mapping;

int32_t *matrix_A;
int32_t *matrix_B;

uint32_t rep_count;

systolic_matrix_t *syst_matrix_A;
systolic_matrix_t *syst_matrix_B;
systolic_matrix_t *syst_matrix_C;

void generate_gradient_matrix(int32_t **matrix, uint32_t num_rows,
                              uint32_t num_cols) {
  int32_t *new_matrix =
      (int32_t *)simple_malloc(num_rows * num_cols * sizeof(int32_t));
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
  mempool_init(core_id, num_cores);

  // Allocate systolic grid mapping
  if (core_id == 0) {
    grid_mapping = (uint32_t *)simple_malloc(num_cores * sizeof(uint32_t));
    if (num_cores != SYSTOLIC_SIZE * SYSTOLIC_SIZE) {
      printf("SYSTOLIC_SIZE does not match core count!\n");
      return -1;
    }
  }

  // Assign grid position (row wise)
  // uint32_t col_idx = core_id % SYSTOLIC_SIZE;
  // uint32_t row_idx = core_id / SYSTOLIC_SIZE;

  // Assign grid position (col wise)
  uint32_t col_idx = core_id / SYSTOLIC_SIZE;
  uint32_t row_idx = core_id % SYSTOLIC_SIZE;

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
    // print_matrix((int32_t *)grid_mapping, 16, 16);

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

  // Wait for all cores
  mempool_barrier(num_cores);

  if ((row_idx == 0) && (col_idx == 0)) {
    // Top left corner
    // row and column producing processing element
    systolic_rcp_pe(rep_count, syst_matrix_A, syst_matrix_B, syst_matrix_C);
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    // Top row
    // column producing processing element
    systolic_cp_pe(col_idx, rep_count, syst_matrix_B, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    // Leftmost column
    // row producing processing element
    systolic_rp_pe(row_idx, rep_count, syst_matrix_A, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    // Remainder
    // non-producing processing element
    systolic_np_pe(row_idx, col_idx, rep_count, syst_matrix_C);
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    // Stop benchmark
    mempool_stop_benchmark();
    printf("> End\n");

    // Print out systolic matrix C
    // printf("> Print Systolic Matrix C\n");
    // systolic_matrix_print(syst_matrix_C);

    // Print out benchmark results
    // systolic_benchmark_print();
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
