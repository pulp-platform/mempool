// Copyright 2023 ETH Zurich and University of Bologna.
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

// Author: Sergio Mazzola, ETH Zurich
//         Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "systolic/conv_qlr_3.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Settings
#define VERIFY_OUTPUT  1
#define PRINTF_MATRIX  0
#define PRINTF_VERBOSE 1

// Global variables
uint32_t *core_map;
int32_t *matrix_X;
int32_t *matrix_Y;
const int32_t weights[K][K] = {{1, 2, 1}, {2, 4, 2}, {1, 2, 1}};
// Tile-local matrix for weights
int32_t *matrix_W[NUM_CORES / NUM_CORES_PER_TILE];

/// Fill @param matrix with a custom gradient, parallelizing row-wise
void fill_matrix_gradient(int32_t *matrix,
                          uint32_t num_rows, uint32_t num_cols,
                          uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_cols; j++) {
      matrix[i * num_cols + j] = ((int32_t)i % 16) + ((int32_t)j % 4);
    }
  }
}

/// Reset @param matrix to 0, parallelizing row-wise
void reset_matrix(int32_t *matrix,
                  uint32_t num_rows, uint32_t num_cols,
                  uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_cols; j++) {
      matrix[i * num_cols + j] = 0;
    }
  }
}

void print_matrix(int32_t *matrix, uint32_t num_rows,
                  uint32_t num_cols) {
  printf("Matrix at 0x%08X\n", (uint32_t)matrix);
  for (uint32_t i = 0; i < num_rows; i++) {
    for (uint32_t j = 0; j < num_cols; j++) {
      printf("%5d ", matrix[i * num_cols + j]);
    }
    printf("\n");
  }
}

#if VERIFY_OUTPUT
typedef struct {
  uint32_t error;
  uint32_t i;
  uint32_t j;
  int32_t wrong_value;
  int32_t golden_value;
} error_verif_t;

error_verif_t error_verif[NUM_CORES];

/// Verify @param C matmul output parallelizing row-wise
int verify_matrix(int32_t *X, uint32_t num_rows, uint32_t num_cols,
                  uint32_t core_id, uint32_t num_cores) {
  error_verif[core_id].error = 0;
  // do not consider halo
  for (uint32_t i = core_id + 1; i < num_rows - 1; i += num_cores) {
    int32_t x, y;
    // determine y
    if (i % 16 == 0)
      y = 4;
    else if (i % 16 == 15)
      y = 11;
    else
      y = (int32_t)i % 16;
    for (uint32_t j = 1; j < num_cols - 1; j++) {
      // determine x
      x = (((int32_t)j % 4) / 2) + 1;
      int32_t golden = x + y;
      // systolic conv does not do division by sum(weights)
      int32_t x_div_w = X[i * num_cols + j]/16;
      // Check correctness (do not check halo)
      if (golden != x_div_w) {
          error_verif[core_id].error = 1;
          error_verif[core_id].i = i;
          error_verif[core_id].j = j;
          error_verif[core_id].wrong_value = x_div_w;
          error_verif[core_id].golden_value = golden;
          return 1;
      }
    }
  }
  return 0;
}
#endif

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t tile_id = core_id / NUM_CORES_PER_TILE;
  // Systolic convolution chain
  uint32_t chain_id = core_id / SYSTOLIC_LENGTH;
  uint32_t num_chains = num_cores / SYSTOLIC_LENGTH;

  // Initialization
  mempool_barrier_init(core_id);
  mempool_init(core_id);

  // Allocate core map
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
  // Wait for all cores
  mempool_barrier(num_cores);

  // Set core map
  core_map[core_id] = core_id;
  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("Initialize\n");
    #endif

    #if PRINTF_MATRIX
    // Print out core mapping
    print_matrix((int32_t *)core_map, 1, num_cores);
    #endif

    // Initialize systolic array
    systolic_init(core_map);

    // Allocate in and out matrices
    #if PRINTF_VERBOSE
    printf("Allocating matrix X...\n");
    #endif
    matrix_X = (int32_t *)simple_malloc(DIM_M * DIM_N * sizeof(int32_t));
    #if PRINTF_VERBOSE
    printf("Allocating matrix Y...\n");
    #endif
    matrix_Y = (int32_t *)simple_malloc(DIM_M * DIM_N * sizeof(int32_t));
    if ((matrix_X == NULL) || (matrix_Y == NULL)) {
      printf("ERROR: failed to allocate matrices\n");
      return -1;
    }
  }
  // Wait for all cores
  mempool_barrier(num_cores);

  // Initialize output to 0
  // (prevents problem in verification/printing)
  reset_matrix(matrix_Y, DIM_M, DIM_N, core_id, num_cores);
  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup: Distribute weights (only first core of each tile)
  if (core_id % NUM_CORES_PER_TILE == 1) {
    // Get tile allocator
    alloc_t *tile_alloc = get_alloc_tile(tile_id);

    // Allocate local matrix_W
    matrix_W[tile_id] = (int32_t *)domain_malloc(tile_alloc, K*K * sizeof(int32_t));

    // Load weights into tile local memory banks
    for (uint32_t y = 0; y < K; ++y)
      for (uint32_t x = 0; x < K; ++x)
        (matrix_W[tile_id])[y * K + x] = weights[y][x];
  }
  // Wait for all cores
  mempool_barrier(num_cores);

  // Fill input matrix
  fill_matrix_gradient(matrix_X, DIM_M, DIM_N, core_id, num_cores);
  // weights matrix already hardcoded to {{1, 2, 1}, {2, 4, 2}, {1, 2, 1}}

  // Start message
  if (core_id == 0) {
    #if PRINTF_MATRIX
    // Print matrix X
    print_matrix(matrix_X, DIM_M, DIM_N);
    // Print matrix W
    print_matrix((int32_t *)weights, K, K);
    #endif

    #if PRINTF_VERBOSE
    printf("Start\n");
    #endif
  }
  mempool_barrier(num_cores);

  // Start benchmark for all cores
  mempool_start_benchmark();

  // based on where is the core in a chain of SYSTOLIC_LENGTH PEs
  switch (core_id % SYSTOLIC_LENGTH) {
    // front core of a chain
    case 0:
      systolic_conv_front(core_id, chain_id, num_chains, num_cores,
                          DIM_M, DIM_N, matrix_X,
                          REP_COUNT);
      break;
    // final core of a chain
    case (SYSTOLIC_LENGTH - 1):
      systolic_conv_end(core_id, chain_id, num_chains, num_cores,
                        DIM_M, DIM_N, matrix_X,
                        matrix_W[tile_id], matrix_Y,
                        REP_COUNT);
      break;
    // cores internal to the each chain
    default:
      systolic_conv_mid(core_id, chain_id, num_chains, num_cores,
                        DIM_M, DIM_N, matrix_X,
                        matrix_W[tile_id], matrix_Y,
                        REP_COUNT);
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
    // Print out matrix Y
    print_matrix(matrix_Y, DIM_M, DIM_N);
    #endif
  }
  mempool_barrier(num_cores);

  // Verify result
  #if VERIFY_OUTPUT
  #if PRINTF_VERBOSE
  if (core_id == 0)
    printf("Verifying result...\n");
  #endif
  verify_matrix(matrix_Y, DIM_M, DIM_N, core_id, num_cores);
  mempool_barrier(num_cores);

  // return the index of the first error
  if (core_id == 0){
    uint32_t min_error_core_id = 0;
    uint32_t min_error_i = UINT32_MAX;
    for (uint32_t c = 0; c < num_cores; c++) {
      if (error_verif[c].error) {
        if (error_verif[c].i * DIM_N + error_verif[c].j < min_error_i) {
          min_error_i = error_verif[c].i * DIM_N + error_verif[c].j;
          min_error_core_id = c;
        }
      }
    }
    // if found, then print out and return error index
    if (error_verif[min_error_core_id].error) {
      printf("ERROR: wrong value at X[%d][%d] == X[%d]: %d (golden == %d)\n",
             error_verif[min_error_core_id].i,
             error_verif[min_error_core_id].j,
             error_verif[min_error_core_id].i * DIM_N + error_verif[min_error_core_id].j,
             error_verif[min_error_core_id].wrong_value,
             error_verif[min_error_core_id].golden_value);
      return (error_verif[min_error_core_id].i + error_verif[min_error_core_id].j) == 0 ?
        -1 : (int)(error_verif[min_error_core_id].i * DIM_N + error_verif[min_error_core_id].j);
    }
  }
  #endif

  // Wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
