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
//         Sergio Mazzola, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "systolic/matmul_qlr_3x4.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Dimensions of matrices
// A = M x N, B = N x P, C = M x N

// M and P must be multiples of 'degree of unrolling'
// e.g., degree of unrolling = 3 if every PE computes a 3x3 output chunk
// For better performance, multiple of 'systolic size' * 'degree of unrolling'
// N can be any value; N >> M, N >> P is recommended for compute-boundness

// Note that 'systolic size' and 'degree of unrolling' might be different
// based on the considered dimension (row, column)

#ifndef DIM_M
#define DIM_M 96
#endif
#ifndef DIM_N
// inner dimension
#define DIM_N 20
#endif
#ifndef DIM_P
#define DIM_P 128
#endif

// Settings
#define TOPOLOGY       1
#define VERIFY_OUTPUT  0
#define PRINTF_MATRIX  0
#define PRINTF_VERBOSE 0

// Global variables
uint32_t *core_map;
int32_t *matrix_A;
int32_t *matrix_B;
int32_t *matrix_C;

/// Fill @param matrix with a gradient in a parallelized way:
/// each core fills all the rows of index y = core_id + i*num_cores
void fill_gradient_matrix(int32_t *matrix, uint32_t num_rows,
                          uint32_t num_cols, uint32_t core_id,
                          uint32_t num_cores) {
  for (uint32_t y = core_id; y < num_rows; y += num_cores) {
    for (uint32_t x = 0; x < num_cols; x++) {
      matrix[y * num_cols + x] = (int32_t)(y + x);
    }
  }
}

void print_matrix(int32_t const *matrix, uint32_t num_rows,
                  uint32_t num_columns) {
  printf("Matrix at 0x%8X\n", (uint32_t)matrix);
  for (uint32_t i = 0; i < num_rows; i++) {
    for (uint32_t j = 0; j < num_columns; j++) {
      printf("%5d ", matrix[i * num_columns + j]);
    }
    printf("\n");
  }
}

/// Verify @param C matmul output parallelizing row-wise
int verify_matrix(int32_t const *A, int32_t const *B, int32_t const *C,
                  uint32_t num_rows, uint32_t inner_dim, uint32_t num_columns,
                  uint32_t num_cores) {
  for (uint32_t i = 0; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      int32_t golden = 0;
      for (uint32_t n = 0; n < inner_dim; n++) {
        golden += A[i * inner_dim + n] * B[n * num_columns + j];
      }
      if (golden != C[i * num_columns + j]){
        #if PRINTF_VERBOSE
        printf("ERROR: matrix_C[%d] = %d (instead of %d)\n", i * num_columns + j, C[i * num_columns + j], golden);
        #endif
        return i * num_columns + j == 0 ? -1 : (int)(i * num_columns + j);
      }
    }
  }
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t tile_id = core_id / NUM_CORES_PER_TILE;
  uint32_t group_id = tile_id / NUM_TILES_PER_GROUP;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id);

  // Allocate systolic grid mapping
  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("Allocating core map...\n");
    #endif
    core_map = (uint32_t *)simple_malloc(num_cores * sizeof(uint32_t));
    if (core_map == NULL) {
      printf("ERROR: failed to allocate core map\n");
      return -1;
    }
  }

  // Systolic cores mapping
  //NOTE: SYSTOLIC_SIZE, NUM_CORES_PER_TILE, and NUM_TILES_PER_GROUP must be perfect squares

#if TOPOLOGY == 0 /* SQUARE */
  // Column index (x):
  // get id of tile section based on how many tile sections per row
  uint32_t col_idx = tile_id % (SYSTOLIC_SIZE / SQRT_NUM_CORES_PER_TILE);
  // jump to the correct 'x' based on the tile section id and width
  col_idx *= SQRT_NUM_CORES_PER_TILE;
  // inside this tile section, jump to the correct 'x' based on the core id
  col_idx += core_id % SQRT_NUM_CORES_PER_TILE;

  // Row index (y):
  // tile sections are placed in a row-wise fashion based on tile id, so to
  // get the row tile section id you must divide instead of doing modulo
  uint32_t row_idx = tile_id / (SYSTOLIC_SIZE / SQRT_NUM_CORES_PER_TILE);
  // as above, jumps to the correct 'y' based on tile section width
  row_idx *= SQRT_NUM_CORES_PER_TILE;
  // gets correct 'y' offset based on core id
  row_idx += (core_id % NUM_CORES_PER_TILE) / SQRT_NUM_CORES_PER_TILE;
#elif TOPOLOGY == 1 /* SQUARE SQUARE */
  // Column index (x):
  // horizontal position of group section = group id % how many group sections fit in one row
  uint32_t col_idx = group_id % (SYSTOLIC_SIZE / (SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE));
  // group section base 'x' = horizontal position * width of a group section (= tiles per group * width tile section)
  col_idx *= SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE;
  // add tile 'x' offset in the group section based on group section and tile section widths
  col_idx += (tile_id % SQRT_NUM_TILES_PER_GROUP) * SQRT_NUM_CORES_PER_TILE;
  // add core 'x' offset in each tile section
  col_idx += core_id % SQRT_NUM_CORES_PER_TILE;

  // Row index (y):
  // vertical position of group section = group id / how many group sections fit in one row
  uint32_t row_idx = group_id / (SYSTOLIC_SIZE / (SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE));
  // group section base 'y' = vertical position * width of a group section (= tiles per group * width tile section)
  row_idx *= SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE;
  // add tile 'y' offset in the group section based on group section and tile section widths
  row_idx += ((tile_id % NUM_TILES_PER_GROUP) / SQRT_NUM_TILES_PER_GROUP) * SQRT_NUM_CORES_PER_TILE;
  // add core 'y' offset in each tile section
  row_idx += (core_id % NUM_CORES_PER_TILE) / SQRT_NUM_CORES_PER_TILE;
#else
#error Unsupported topology.
#endif

  // Wait for all cores
  mempool_barrier(num_cores);

  // Set tile and core mapping
  core_map[row_idx * SYSTOLIC_SIZE + col_idx] = core_id;

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("Initialize\n");
    #endif

    #if PRINTF_MATRIX
    // Print out core mapping
    print_matrix((int32_t *)core_map, SYSTOLIC_SIZE, SYSTOLIC_SIZE);
    #endif

    // Initialize systolic array
    systolic_init(core_map);

    // Create matrices
    #if PRINTF_VERBOSE
    printf("Allocating matrix A...\n");
    #endif
    matrix_A = (int32_t *)simple_malloc(DIM_M * DIM_N * sizeof(int32_t));
    #if PRINTF_VERBOSE
    printf("Allocating matrix B...\n");
    #endif
    matrix_B = (int32_t *)simple_malloc(DIM_N * DIM_P * sizeof(int32_t));
    #if PRINTF_VERBOSE
    printf("Allocating matrix C...\n");
    #endif
    matrix_C = (int32_t *)simple_malloc(DIM_M * DIM_P * sizeof(int32_t));
    if ((matrix_A == NULL) || (matrix_B == NULL) || (matrix_C == NULL)) {
      printf("ERROR: failed to allocate matrices\n");
      return -1;
    }
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Fill matrices with gradient
  fill_gradient_matrix(matrix_A, DIM_M, DIM_N, core_id, num_cores);
  fill_gradient_matrix(matrix_B, DIM_N, DIM_P, core_id, num_cores);

  // Start message
  if (core_id == 0) {
    #if PRINTF_MATRIX
    // Print out matrices A & B
    print_matrix(matrix_A, DIM_M, DIM_N);
    print_matrix(matrix_B, DIM_N, DIM_P);
    #endif

    #if PRINTF_VERBOSE
    printf("Start\n");
    #endif
  }

  // Start benchmark for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  if ((row_idx == 0) && (col_idx == 0)) {
    systolic_rcp_pe(DIM_M, DIM_N, DIM_P, matrix_A, matrix_B, matrix_C);
  }

  if ((row_idx == 0) && (col_idx != 0)) {
    systolic_cp_pe(col_idx, DIM_M, DIM_N, DIM_P, matrix_B, matrix_C);
  }

  if ((row_idx != 0) && (col_idx == 0)) {
    systolic_rp_pe(row_idx, DIM_M, DIM_N, DIM_P, matrix_A, matrix_C);
  }

  if ((row_idx != 0) && (col_idx != 0)) {
    systolic_np_pe(row_idx, col_idx, DIM_M, DIM_N, DIM_P, matrix_C);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("End\n");
    #endif

    #if PRINTF_MATRIX
    // Print out matrix C
    print_matrix(matrix_C, DIM_M, DIM_P);
    #endif

    #if VERIFY_OUTPUT
    // Verify result
    #if PRINTF_VERBOSE
    printf("Verifying result...\n");
    #endif
    int ret = verify_matrix(matrix_A, matrix_B, matrix_C, DIM_M, DIM_N, DIM_P, num_cores);
    if(ret)
      return ret;
    #endif
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
