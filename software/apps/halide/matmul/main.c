// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "encoding.h"
#include "halide_pipeline.riscv.h"
#include "halide_runtime.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <stdint.h>
#include <string.h>

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#define matrix_M 16
#define matrix_N 16
#define matrix_P 16
// #define VERBOSE

int32_t matrix_a[matrix_M * matrix_N] __attribute__((section(".l1")));
int32_t matrix_b[matrix_N * matrix_P] __attribute__((section(".l1")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1")));

volatile halide_buffer_t halide_buffer_matrix_a __attribute__((section(".l1")));
volatile halide_buffer_t halide_buffer_matrix_b __attribute__((section(".l1")));
volatile halide_buffer_t halide_buffer_matrix_c __attribute__((section(".l1")));

halide_dimension_t buffer_dim_matrix_a[2] __attribute__((section(".l1")));
halide_dimension_t buffer_dim_matrix_b[2] __attribute__((section(".l1")));
halide_dimension_t buffer_dim_matrix_c[2] __attribute__((section(".l1")));

struct halide_type_t buffer_type __attribute__((section(".l1")));

int volatile error __attribute__((section(".l1")));

void init_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                 int32_t a, int32_t b, int32_t c, uint32_t core_id,
                 uint32_t num_cores) {
  uint32_t const split = 8; // How many rows/columns to split the matrix into
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

// Initialize the matrices in parallel
int verify_matrix(int32_t *matrix, uint32_t num_rows, uint32_t num_columns,
                  uint32_t inner_dim, int32_t aa, int32_t ab, int32_t ac,
                  int32_t ba, int32_t bb, int32_t bc, uint32_t core_id,
                  uint32_t num_cores) {
  // Convert to signed
  int32_t n = (int32_t)inner_dim;
  // Parallelize over rows
  for (uint32_t i = core_id; i < num_rows; i += num_cores) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      int32_t ii = (int32_t)i;
      int32_t jj = (int32_t)j;
      int32_t lin =
          (aa * bb * ii * jj + aa * bc * ii + ac * bb * jj + ac * bc) * n;
      int32_t qua =
          ((aa * ba * ii + ab * bb * jj + ab * bc + ba * ac) * (n * (n - 1))) /
          2;
      int32_t cub = ((ab * ba) * (n * (n - 1) * (2 * n - 1))) / 6;
      int32_t golden = lin + qua + cub;
      if (matrix[i * num_columns + j] != golden) {
        return (i + j) == 0 ? -1 : (int)(i * num_columns + j);
      }
      matrix[i * num_columns + j] = 0;
    }
  }
  return 0;
}

int halide_matmul(uint32_t core_id, uint32_t num_cores) {

  if (core_id == 0) {
    // Specify a two-dimensional buffers
    buffer_dim_matrix_a[0].min = 0;
    buffer_dim_matrix_a[0].extent = matrix_M;
    buffer_dim_matrix_a[0].stride = 1;
    buffer_dim_matrix_a[0].flags = 0;
    buffer_dim_matrix_a[1].min = 0;
    buffer_dim_matrix_a[1].extent = matrix_N;
    buffer_dim_matrix_a[1].stride = buffer_dim_matrix_a[0].extent;
    buffer_dim_matrix_a[1].flags = 0;

    buffer_dim_matrix_b[0].min = 0;
    buffer_dim_matrix_b[0].extent = matrix_N;
    buffer_dim_matrix_b[0].stride = 1;
    buffer_dim_matrix_b[0].flags = 0;
    buffer_dim_matrix_b[1].min = 0;
    buffer_dim_matrix_b[1].extent = matrix_P;
    buffer_dim_matrix_b[1].stride = buffer_dim_matrix_b[0].extent;
    buffer_dim_matrix_b[1].flags = 0;

    buffer_dim_matrix_c[0].min = 0;
    buffer_dim_matrix_c[0].extent = matrix_M;
    buffer_dim_matrix_c[0].stride = 1;
    buffer_dim_matrix_c[0].flags = 0;
    buffer_dim_matrix_c[1].min = 0;
    buffer_dim_matrix_c[1].extent = matrix_P;
    buffer_dim_matrix_c[1].stride = buffer_dim_matrix_c[0].extent;
    buffer_dim_matrix_c[1].flags = 0;

    // Specify the type of data in the buffer
    buffer_type.code = halide_type_int;
    buffer_type.bits = 32;
    buffer_type.lanes = 1;

    // Assign all parameters to the buffer structures
    halide_buffer_matrix_a.device = 0;
    halide_buffer_matrix_a.device_interface = NULL;
    halide_buffer_matrix_a.host = (uint8_t *)&matrix_a;
    halide_buffer_matrix_a.flags = 1;
    halide_buffer_matrix_a.type = buffer_type;
    halide_buffer_matrix_a.dimensions = 2;
    halide_buffer_matrix_a.dim = (halide_dimension_t *)buffer_dim_matrix_a;
    halide_buffer_matrix_a.padding = 0;

    halide_buffer_matrix_b.device = 0;
    halide_buffer_matrix_b.device_interface = NULL;
    halide_buffer_matrix_b.host = (uint8_t *)&matrix_b;
    halide_buffer_matrix_b.flags = 1;
    halide_buffer_matrix_b.type = buffer_type;
    halide_buffer_matrix_b.dimensions = 2;
    halide_buffer_matrix_b.dim = (halide_dimension_t *)buffer_dim_matrix_b;
    halide_buffer_matrix_b.padding = 0;

    halide_buffer_matrix_c.device = 0;
    halide_buffer_matrix_c.device_interface = NULL;
    halide_buffer_matrix_c.host = (uint8_t *)&matrix_c;
    halide_buffer_matrix_c.flags = 1;
    halide_buffer_matrix_c.type = buffer_type;
    halide_buffer_matrix_c.dimensions = 2;
    halide_buffer_matrix_c.dim = (halide_dimension_t *)buffer_dim_matrix_c;
    halide_buffer_matrix_c.padding = 0;
  }

  mempool_barrier(num_cores);

  mempool_start_benchmark();
  // Call the Halide pipeline
  int error = halide_pipeline((halide_buffer_t *)&halide_buffer_matrix_a,
                              (halide_buffer_t *)&halide_buffer_matrix_b,
                              (halide_buffer_t *)&halide_buffer_matrix_c);
  mempool_stop_benchmark();

  mempool_barrier(num_cores);
#ifdef VERBOSE
  if (core_id == 0) {
    // Print the result
    printf("Matmul finished with exit code %d\n", error);
    for (int y = 0; y < buffer_dim_matrix_c[1].extent; ++y) {
      for (int x = 0; x < buffer_dim_matrix_c[0].extent; ++x) {
        uint32_t val = ((uint32_t *)halide_buffer_matrix_c
                            .host)[x * buffer_dim_matrix_c[0].stride +
                                   y * buffer_dim_matrix_c[1].stride];
        printf("%5d ", val);
      }
      printf("\n");
    }
  }
#endif

  return error;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
  }

  int32_t const A_a = 1;
  int32_t const A_b = 1;
  int32_t const A_c = -32;
  int32_t const B_a = 2;
  int32_t const B_b = 1;
  int32_t const B_c = 16;

  // Initialize Matrices
  mempool_start_benchmark();

  init_matrix(matrix_a, matrix_M, matrix_N, A_a, A_b, A_c, core_id, num_cores);
  init_matrix(matrix_b, matrix_N, matrix_P, B_a, B_b, B_c, core_id, num_cores);

  // Initialized --> Start calculating (implicit barrier at start)
  mempool_start_benchmark();
  halide_matmul(core_id, num_cores);

  // wait until all cores have finished
  mempool_barrier(num_cores);

  if (verify_matrix(matrix_c, matrix_M, matrix_P, matrix_N, A_a, A_b, A_c, B_a,
                    B_b, B_c, core_id, num_cores)) {
    error = 1;
    return -1;
  }

  mempool_barrier(num_cores);

  return error;
}
