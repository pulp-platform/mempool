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
#include "systolic/matmul_xqueue.h"

// Dimensions of matrices
#define DIM_M 96
#define DIM_N 96
#define DIM_P 96

uint32_t *tile_mapping;
uint32_t *core_mapping;

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
    tile_mapping = (uint32_t *)simple_malloc(num_cores * 4);
    core_mapping = (uint32_t *)simple_malloc(num_cores * 4);
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
  // uint32_t col_idx = tile_id % 2;
  // col_idx *= 2;
  // col_idx += core_id % 2;
  // uint32_t row_idx = tile_id / 2;
  // row_idx *= 2;
  // row_idx += (core_id % 4) / 2;
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
  tile_mapping[row_idx * SYSTOLIC_SIZE + col_idx] = tile_id;
  core_mapping[row_idx * SYSTOLIC_SIZE + col_idx] = core_id;

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("> Initialize\n");

    // Print out tile mapping
    // print_matrix((int32_t *)tile_mapping, SYSTOLIC_SIZE, SYSTOLIC_SIZE);

    // Print out core mapping
    // print_matrix((int32_t *)core_mapping, SYSTOLIC_SIZE, SYSTOLIC_SIZE);

    // Initialize systolic array
    systolic_init(tile_mapping, core_mapping);

    // Create systolic matrices
    systolic_matrix_allocate(&syst_matrix_A, DIM_M, DIM_N);
    systolic_matrix_allocate(&syst_matrix_B, DIM_N, DIM_P);
    systolic_matrix_allocate(&syst_matrix_C, DIM_M, DIM_P);

    // Set repetition count per submatrix of C (A->num_cols == B->num_rows)
    rep_count = syst_matrix_A->num_cols / 2;
  }

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  // Fill matrices with gradient
  fill_systolic_matrix(syst_matrix_A, core_id, num_cores);
  fill_systolic_matrix(syst_matrix_B, core_id, num_cores);

  // Wait for all cores
  mempool_sleep_barrier(num_cores);

  if (core_id == 0) {
    printf("> Start\n");
  }

  // Start benchmark for all cores
  mempool_sleep_barrier(num_cores);
  mempool_start_benchmark();

  if ((row_idx == 0) && (col_idx == 0)) {
    systolic_rcp_pe(num_cores, rep_count, syst_matrix_A, syst_matrix_B,
                    syst_matrix_C);
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    systolic_cp_pe(num_cores, col_idx, rep_count, syst_matrix_B, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    systolic_rp_pe(num_cores, row_idx, rep_count, syst_matrix_A, syst_matrix_C);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    systolic_np_pe(num_cores, row_idx, col_idx, rep_count, syst_matrix_C);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_sleep_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    printf("> End\n");

    // Print out systolic matrix C
    // printf("> Print Systolic Matrix C\n");
    // systolic_matrix_print(syst_matrix_C);
  }

  // wait until all cores have finished
  mempool_sleep_barrier(num_cores);
  return 0;
}
