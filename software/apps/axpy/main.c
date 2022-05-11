// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yichao Zhang, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/axpy.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <stdlib.h>

#if NUM_CORES > 32
#define size_M 32
#define size_N 32
#else
#define size_M (NUM_CORES)
#define size_N (NUM_CORES)
#endif

#define ALPHA 2

#if NUM_CORES > 32
int32_t data_x[size_M * size_N]
    __attribute__((aligned(64 * 1024), section(".l1")));
int32_t data_y[size_M * size_N]
    __attribute__((aligned(64 * 1024), section(".l1")));
int32_t data_y_copy[size_M * size_N]
    __attribute__((aligned(64 * 1024), section(".l1")));
#else
int32_t data_x[size_M * size_N] __attribute__((aligned(32), section(".l1")));
int32_t data_y[size_M * size_N] __attribute__((aligned(32), section(".l1")));
int32_t data_y_copy[size_M * size_N]
    __attribute__((aligned(32), section(".l1")));
#endif

int volatile error __attribute__((section(".l1")));

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  // How many rows/columns to split the matrix into
  uint32_t const split = 8;
  if (num_columns > num_rows) {
    // Parallelize over columns
    uint32_t const c_start = (num_rows / split) * (core_id % split);
    uint32_t const c_end = (num_rows / split) * ((core_id % split) + 1);
    for (uint32_t j = (core_id / split); j < num_columns;
         j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (num_columns / split) * (core_id % split);
    uint32_t const c_end = (num_columns / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < num_rows;
         i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        matrix[i * num_columns + j] = a * (int32_t)i + b * (int32_t)j + c;
      }
    }
  }
}

int verify_axpy(int32_t *matrix_X, int32_t *matrix_Y, int32_t *matrix_Y_COPY,
                int32_t alpha, uint32_t elements) {
  for (uint32_t i = 0; i < elements; i++) {
    if (matrix_Y[i] != matrix_X[i] * alpha + matrix_Y_COPY[i]) {
      return 1;
    }
  }
  return 0;
}

// Serial calculation by core 0
void calc_axpy_serial(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
                      uint32_t elements, uint32_t core_id) {
  if (core_id == 0) {
    AXPY(elements, alpha, &matrix_X[0], &matrix_Y[0]);
  }
}

// Serial calculation with 4 time unloop by core 0
void calc_axpy_serial_unloop(int32_t *matrix_X, int32_t *matrix_Y,
                             int32_t alpha, uint32_t elements,
                             uint32_t core_id) {
  if (core_id == 0) {
    AXPY_unloop(elements, alpha, &matrix_X[0], &matrix_Y[0]);
  }
}

// Parallel calculation
void calc_axpy(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
               uint32_t elements, uint32_t core_id, uint32_t num_cores) {
  // Support the elements number is not the devided by the core numbers;
  // The corresponding core ID will take the partial elements.
  uint32_t split = elements / num_cores;
  uint32_t partial = elements % num_cores;
  if (core_id < partial) {
    uint32_t const c_start = core_id * (split + 1);
    uint32_t const j = split + 1;
    AXPY(j, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  } else {
    uint32_t const c_start = core_id * split + partial;
    AXPY(split, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  }
}

// Parallel calculation with 4 times unloop
void calc_axpy_unloop(int32_t *matrix_X, int32_t *matrix_Y, int32_t alpha,
                      uint32_t elements, uint32_t core_id, uint32_t num_cores) {
  // Support the elements number is not the devided by the core numbers;
  // The corresponding core ID will take the partial elements.
  uint32_t split = elements / num_cores;
  uint32_t partial = elements % num_cores;
  if (core_id < partial) {
    uint32_t const c_start = core_id * (split + 1);
    uint32_t const j = split + 1;
    AXPY_unloop(j, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  } else {
    uint32_t const c_start = core_id * split + partial;
    AXPY_unloop(split, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
  }
}

// Parallel calculation with 4 times unloop align with banks
void calc_axpy_unloop_x4_localbank(int32_t *matrix_X, int32_t *matrix_Y,
                                   int32_t alpha, uint32_t elements,
                                   uint32_t core_id, uint32_t num_cores) {
  uint32_t const bank_num = num_cores * 4;
  // Do the calculation that redundant elements cannot be unloop;
  // Use core0 is less overhead than found the local
  uint32_t partial = elements % 4;
  if (core_id == 0) {
    if (partial != 0) {
      uint32_t c_start = elements - partial + 1;
      AXPY(partial, alpha, &matrix_X[c_start], &matrix_Y[c_start]);
    }
  }
  // Do unloop 4 times
  uint32_t const total_unloop = elements - partial;
  uint32_t const c_start = core_id * 4;
  for (uint32_t c = c_start; c <= total_unloop - 4; c += bank_num) {
    AXPY_unloop_x4(alpha, &matrix_X[c], &matrix_Y[c]);
  }
}

int main() {

  uint32_t const core_id = mempool_get_core_id();
  uint32_t const num_cores = mempool_get_core_count();
  uint32_t const total_elements = size_M * size_N;

  // Seed for create element matrix
  int32_t const A_a = 1;
  int32_t const A_b = 1;
  int32_t const A_c = -32;
  int32_t const B_a = 2;
  int32_t const B_b = 1;
  int32_t const B_c = 16;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);
  if (core_id == 0) {
    printf("Initialize %3d cores\n", num_cores);
    error = 0;
  }

  // init_elements;
  init_matrix(data_x, size_M, size_N, A_a, A_b, A_c, core_id, num_cores);
  init_matrix(data_y, size_M, size_N, B_a, B_b, B_c, core_id, num_cores);
  init_matrix(data_y_copy, size_M, size_N, B_a, B_b, B_c, core_id, num_cores);
  mempool_barrier(num_cores);

  // start kernel testing
  // benchmark three time to aviod last memory access on the barrier boundary
  mempool_start_benchmark();
  calc_axpy_unloop_x4_localbank(data_x, data_y, ALPHA, total_elements, core_id,
                                num_cores);
  mempool_start_benchmark();
  calc_axpy_unloop_x4_localbank(data_x, data_y, ALPHA, total_elements, core_id,
                                num_cores);
  mempool_start_benchmark();
  calc_axpy_unloop_x4_localbank(data_x, data_y, ALPHA, total_elements, core_id,
                                num_cores);
  mempool_stop_benchmark();
  // end kernel testing
  mempool_barrier(num_cores);

  // Verify results
  if (core_id == 0) {
    printf("START CHECKING RESULTS\n");
    if (verify_axpy(data_x, data_y, data_y_copy, ALPHA, total_elements)) {
      printf("RESULTS ERROR\n");
      error = 1;
    } else {
      printf("RESULTS CORRECT\n");
    }
  }
  mempool_barrier(num_cores);

  return error;
}
