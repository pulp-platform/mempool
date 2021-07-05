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

#define N 16
#define M 16
#define KERNEL_N 3
#define PADDING (KERNEL_N / 2)
// #define VERBOSE

volatile uint32_t in[N][M] __attribute__((section(".l1")));
volatile uint32_t out[N][M] __attribute__((section(".l1")));
volatile halide_buffer_t halide_buffer_in __attribute__((section(".l1")));
volatile halide_buffer_t halide_buffer_out __attribute__((section(".l1")));
halide_dimension_t buffer_dim[2] __attribute__((section(".l1")));
struct halide_type_t buffer_type __attribute__((section(".l1")));
volatile uint32_t kernel[KERNEL_N][KERNEL_N] __attribute__((section(".l1")));

void convolution(uint32_t core_id, uint32_t num_cores) {
  asm volatile("nop" ::);
  uint32_t sum;
  uint32_t(*kernel_stable)[KERNEL_N] = (uint32_t(*)[KERNEL_N])kernel;
  for (uint32_t i = core_id; i < N - KERNEL_N + 1; i += num_cores) {
    for (uint32_t j = 0; j < M - KERNEL_N + 1; j++) {
      sum = 0;
      for (uint32_t k = 0; k < KERNEL_N; k++) {
        for (uint32_t l = 0; l < KERNEL_N; l++) {
          sum += in[i + k][j + l] * kernel_stable[k][l];
        }
      }
      out[i][j] = sum / 16;
    }
  }
  asm volatile("nop" ::);
}

void convolution_unrolled(uint32_t core_id, uint32_t num_cores) {
  asm volatile("nop" ::);
  uint32_t sum;
  uint32_t(*kernel_stable)[KERNEL_N] = (uint32_t(*)[KERNEL_N])kernel;
  for (uint32_t i = core_id; i < N - KERNEL_N + 1; i += num_cores) {
    for (uint32_t j = 0; j < M - KERNEL_N + 1; j++) {
      sum = 0;

      sum += in[i + 0][j + 0] * kernel_stable[0][0];
      sum += in[i + 0][j + 1] * kernel_stable[0][1];
      sum += in[i + 0][j + 2] * kernel_stable[0][2];

      sum += in[i + 1][j + 0] * kernel_stable[1][0];
      sum += in[i + 1][j + 1] * kernel_stable[1][1];
      sum += in[i + 1][j + 2] * kernel_stable[1][2];

      sum += in[i + 2][j + 0] * kernel_stable[2][0];
      sum += in[i + 2][j + 1] * kernel_stable[2][1];
      sum += in[i + 2][j + 2] * kernel_stable[2][2];

      out[i][j] = sum / 16;
    }
  }
  asm volatile("nop" ::);
}

int halide_convolution(uint32_t core_id, uint32_t num_cores) {

  if (core_id == 0) {
    // Specify a two-dimensional buffer
    buffer_dim[0].min = 0;
    buffer_dim[0].extent = M;
    buffer_dim[0].stride = 1;
    buffer_dim[0].flags = 0;
    buffer_dim[1].min = 0;
    buffer_dim[1].extent = N;
    buffer_dim[1].stride = buffer_dim[0].extent;
    buffer_dim[1].flags = 0;

    // Specify the type of data in the buffer
    buffer_type.code = halide_type_uint;
    buffer_type.bits = 32;
    buffer_type.lanes = 1;

    // Assign all parameters to the input buffer structure
    halide_buffer_in.device = 0;
    halide_buffer_in.device_interface = NULL;
    halide_buffer_in.host = (uint8_t *)&in;
    halide_buffer_in.flags = 1;
    halide_buffer_in.type = buffer_type;
    halide_buffer_in.dimensions = 2;
    halide_buffer_in.dim = (halide_dimension_t *)buffer_dim;
    halide_buffer_in.padding = 0;

    // Assign all parameters to the output buffer structure
    halide_buffer_out.device = 0;
    halide_buffer_out.device_interface = NULL;
    halide_buffer_out.host = (uint8_t *)&out;
    halide_buffer_out.flags = 1;
    halide_buffer_out.type = buffer_type;
    halide_buffer_out.dimensions = 2;
    halide_buffer_out.dim = buffer_dim;
    halide_buffer_out.padding = 0;
#ifdef VERBOSE
    printf("Start calculation...\n");
#endif
  }

  mempool_barrier(num_cores, num_cores * 4);

  mempool_start_benchmark();
  // Call the Halide pipeline
  int error = halide_pipeline((halide_buffer_t *)&halide_buffer_in, M, N,
                              (halide_buffer_t *)&halide_buffer_out);
  mempool_stop_benchmark();

  mempool_barrier(num_cores, num_cores * 4);
#ifdef VERBOSE
  // Print the result
  printf("Convolution finished with exit code %d\n", error);
  for (int y = 0; y < buffer_dim[1].extent - 2; ++y) {
    for (int x = 0; x < buffer_dim[0].extent - 2; ++x) {
      uint32_t val =
          ((uint32_t *)halide_buffer_out
               .host)[x * buffer_dim[0].stride + y * buffer_dim[1].stride];
      printf("%3d ", val);
    }
    printf("\n");
  }
#endif

  return error;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
#ifdef VERBOSE
    printf("Initialize\n");
#endif
    kernel[0][0] = 1;
    kernel[0][1] = 2;
    kernel[0][2] = 1;

    kernel[1][0] = 2;
    kernel[1][1] = 4;
    kernel[1][2] = 2;

    kernel[2][0] = 1;
    kernel[2][1] = 2;
    kernel[2][2] = 1;
  }

  // Initialize a and b
  for (uint32_t i = core_id; i < N; i += num_cores) {
    for (uint32_t j = 0; j < M; j++) {
      // in[i][j] = core_id + ((i * i) + 4 * (j % 3) + (j % 9)) % 128;
      in[i][j] = i + j % 128;
    }
  }

  mempool_barrier(num_cores, num_cores * 4);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("A:\n");

    for (int i = 0; i < N; i++) {
      for (int j = 0; j < M; j++) {
        printf("%4u ", in[i][j]);
      }
      printf("\n");
    }

    printf("kernel:\n");
    for (int i = 0; i < KERNEL_N; i++) {
      for (int j = 0; j < KERNEL_N; j++) {
        printf("%4u ", kernel[i][j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(num_cores, num_cores * 4);

  if (core_id == 0) {
    printf("Start\n");
  }
#endif

  // Initialized --> Start calculating
  mempool_start_benchmark();
  convolution(core_id, num_cores);
  mempool_stop_benchmark();

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);

  // Initialized --> Start calculating
  mempool_start_benchmark();
  convolution_unrolled(core_id, num_cores);
  mempool_stop_benchmark();

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);

  // Initialized --> Start calculating
  halide_convolution(core_id, num_cores);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("Done\n");
  }
#endif

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("out:\n");
    for (int i = 0; i < N - KERNEL_N + 1; i++) {
      for (int j = 0; j < M - KERNEL_N + 1; j++) {
        printf("%4u ", out[i][j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(num_cores, num_cores * 4);
#endif

  return 0;
}
