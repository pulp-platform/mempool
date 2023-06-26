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
#include "systolic/matmul_qlr_4x4_hybrid_preload_row.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Settings
#define TOPOLOGY       2
#define VERIFY_OUTPUT  1
#define PRINTF_MATRIX  0
#define PRINTF_VERBOSE 1

// Global variables
uint32_t *core_map;
int32_t *matrix_A;
int32_t *matrix_B;
int32_t *matrix_C;

/// Fill @param matrix with a custom gradient, parallelizing row-wise
void fill_matrix_gradient(int32_t *matrix,
                        uint32_t num_rows, uint32_t num_cols,
                        uint32_t core_id, uint32_t num_cores,
                        int32_t a, int32_t b, int32_t c) {
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_cols; ++j) {
      matrix[i * num_cols + j] = a * (int32_t)i + b * (int32_t)j + c;
    }
  }
}

void print_matrix(int32_t const *matrix, uint32_t num_rows,
                  uint32_t num_cols) {
  printf("Matrix at 0x%08X\n", (uint32_t)matrix);
  for (uint32_t i = 0; i < num_rows; i++) {
    for (uint32_t j = 0; j < num_cols; j++) {
      printf("%5d ", matrix[i * num_cols + j]);
    }
    printf("\n");
  }
}

/// Verify @param C matmul output parallelizing row-wise
int verify_matrix(int32_t const *C,
                  uint32_t num_rows, uint32_t inner_dim, uint32_t num_cols,
                  uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_cols; ++j) {
      // Compute C without looping through inner dim
      int32_t ii = (int32_t)i;
      int32_t jj = (int32_t)j;
      int32_t aa = 1, ab = 1, ac = -32;
      int32_t ba = 2, bb = 1, bc = 16;
      int32_t n = (int32_t)inner_dim;
      int32_t golden = (aa * bb * ii * jj + aa * bc * ii + ac * bb * jj + ac * bc) * n +
              ((aa * ba * ii + ab * bb * jj + ab * bc + ba * ac) * (n * (n - 1))) / 2 +
              ((ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;
      // Check correctness
      if (golden != C[i * num_cols + j]){
        // #if PRINTF_VERBOSE
        // printf("ERROR: matrix_C[%d] = %d (instead of %d)\n", i * num_cols + j, C[i * num_cols + j], golden);
        // #endif
        return (i + j) == 0 ? -1 : (int)(i * num_cols + j);
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

#if TOPOLOGY == 0 /* SQUARE */
  //NOTE: SYSTOLIC_ARRAY_DIM, NUM_CORES_PER_TILE, and NUM_TILES_PER_GROUP must be perfect squares

  // Column index (x):
  // get id of tile section based on how many tile sections per row
  uint32_t col_idx = tile_id % (SYSTOLIC_ARRAY_DIM / SQRT_NUM_CORES_PER_TILE);
  // jump to the correct 'x' based on the tile section id and width
  col_idx *= SQRT_NUM_CORES_PER_TILE;
  // inside this tile section, jump to the correct 'x' based on the core id
  col_idx += core_id % SQRT_NUM_CORES_PER_TILE;

  // Row index (y):
  // tile sections are placed in a row-wise fashion based on tile id, so to
  // get the row tile section id you must divide instead of doing modulo
  uint32_t row_idx = tile_id / (SYSTOLIC_ARRAY_DIM / SQRT_NUM_CORES_PER_TILE);
  // as above, jumps to the correct 'y' based on tile section width
  row_idx *= SQRT_NUM_CORES_PER_TILE;
  // gets correct 'y' offset based on core id
  row_idx += (core_id % NUM_CORES_PER_TILE) / SQRT_NUM_CORES_PER_TILE;

#elif TOPOLOGY == 1 /* SQUARE SQUARE */
  //NOTE: SYSTOLIC_ARRAY_DIM, NUM_CORES_PER_TILE, and NUM_TILES_PER_GROUP must be perfect squares

  // Column index (x):
  // horizontal position of group section = group id % how many group sections fit in one row
  uint32_t col_idx = group_id % (SYSTOLIC_ARRAY_DIM / (SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE));
  // group section base 'x' = horizontal position * width of a group section (= tiles per group * width tile section)
  col_idx *= SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE;
  // add tile 'x' offset in the group section based on group section and tile section widths
  col_idx += (tile_id % SQRT_NUM_TILES_PER_GROUP) * SQRT_NUM_CORES_PER_TILE;
  // add core 'x' offset in each tile section
  col_idx += core_id % SQRT_NUM_CORES_PER_TILE;

  // Row index (y):
  // vertical position of group section = group id / how many group sections fit in one row
  uint32_t row_idx = group_id / (SYSTOLIC_ARRAY_DIM / (SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE));
  // group section base 'y' = vertical position * width of a group section (= tiles per group * width tile section)
  row_idx *= SQRT_NUM_TILES_PER_GROUP * SQRT_NUM_CORES_PER_TILE;
  // add tile 'y' offset in the group section based on group section and tile section widths
  row_idx += ((tile_id % NUM_TILES_PER_GROUP) / SQRT_NUM_TILES_PER_GROUP) * SQRT_NUM_CORES_PER_TILE;
  // add core 'y' offset in each tile section
  row_idx += (core_id % NUM_CORES_PER_TILE) / SQRT_NUM_CORES_PER_TILE;

#elif TOPOLOGY == 2 /* ROW-WISE */
  // Cores of the same tile are on the same systolic grid row

  // Column index (x):
  uint32_t col_idx = core_id % SYSTOLIC_ARRAY_DIM;
  // Row index (y):
  uint32_t row_idx = core_id / SYSTOLIC_ARRAY_DIM;

#else
#error Unsupported topology.
#endif

  // Wait for all cores
  mempool_barrier(num_cores);

  // Set tile and core mapping
  core_map[row_idx * SYSTOLIC_ARRAY_DIM + col_idx] = core_id;

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("Initialize\n");
    #endif

    #if PRINTF_MATRIX
    // Print out core mapping
    print_matrix((int32_t *)core_map, SYSTOLIC_ARRAY_DIM, SYSTOLIC_ARRAY_DIM);
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

  // Fill matrix
  fill_matrix_gradient(matrix_A, DIM_M, DIM_N, core_id, num_cores, 1, 1, -32);
  fill_matrix_gradient(matrix_B, DIM_N, DIM_P, core_id, num_cores, 2, 1, 16);
  // use: a=1, b=1, c=0 for normal, unweighted gradient

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

  if (col_idx == 0) {
    systolic_rp_pe(row_idx, DIM_M, DIM_N, DIM_P, matrix_A);
  } else {
    systolic_np_pe(row_idx, col_idx, DIM_M, DIM_N, DIM_P, matrix_B, matrix_C);
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
  }

  mempool_barrier(num_cores);

  // Verify result
  #if VERIFY_OUTPUT
  #if PRINTF_VERBOSE
  if (core_id == 0)
    printf("Verifying result...\n");
  #endif
  int ret = verify_matrix(matrix_C, DIM_M, DIM_N, DIM_P, core_id, num_cores);
  if(ret)
    return ret;
  #endif

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
