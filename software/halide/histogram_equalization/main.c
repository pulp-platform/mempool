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

// Define Image dimensions:
#define img_width 1024
#define img_height 128
// #define VERBOSE

uint8_t in[img_height * img_width] __attribute__((section(".l1_prio")));

volatile halide_buffer_t halide_buffer_in __attribute__((section(".l1")));

halide_dimension_t buffer_dim_in[2] __attribute__((section(".l1")));

struct halide_type_t buffer_type __attribute__((section(".l1")));

int volatile error __attribute__((section(".l1")));

void init_img(uint8_t *img, uint32_t height, uint32_t width, uint8_t a,
              uint8_t b, uint8_t c, uint32_t core_id, uint32_t num_cores) {
  uint32_t const split = 8; // How many rows/columns to split the img into
  if (width > height) {
    // Parallelize over columns
    uint32_t const c_start = (height / split) * (core_id % split);
    uint32_t const c_end = (height / split) * ((core_id % split) + 1);
    for (uint32_t j = (core_id / split); j < width; j += (num_cores / split)) {
      for (uint32_t i = c_start; i < c_end; ++i) {
        img[i * width + j] = a * (uint8_t)i + b * (uint8_t)j + c;
      }
    }
  } else {
    // Parallelize over rows
    uint32_t const c_start = (width / split) * (core_id % split);
    uint32_t const c_end = (width / split) * ((core_id % split) + 1);
    for (uint32_t i = (core_id / split); i < height; i += (num_cores / split)) {
      for (uint32_t j = c_start; j < c_end; ++j) {
        img[i * width + j] = a * (uint8_t)i + b * (uint8_t)j + c;
      }
    }
  }
}

int halide_histogram_equalization(uint32_t core_id, uint32_t num_cores) {

  if (core_id == 0) {
    // Specify a two-dimensional buffers
    buffer_dim_in[0].min = 0;
    buffer_dim_in[0].extent = img_width;
    buffer_dim_in[0].stride = 1;
    buffer_dim_in[0].flags = 0;
    buffer_dim_in[1].min = 0;
    buffer_dim_in[1].extent = img_height;
    buffer_dim_in[1].stride = buffer_dim_in[0].extent;
    buffer_dim_in[1].flags = 0;

    // Specify the type of data in the buffer
    buffer_type.code = halide_type_uint;
    buffer_type.bits = 8;
    buffer_type.lanes = 1;

    // Assign all parameters to the buffer structures
    halide_buffer_in.device = 0;
    halide_buffer_in.device_interface = NULL;
    halide_buffer_in.host = (uint8_t *)&in;
    halide_buffer_in.flags = 1;
    halide_buffer_in.type = buffer_type;
    halide_buffer_in.dimensions = 2;
    halide_buffer_in.dim = (halide_dimension_t *)buffer_dim_in;
    halide_buffer_in.padding = 0;
  }

  mempool_barrier(num_cores);

  mempool_start_benchmark();
  // Call the Halide pipeline
  if (core_id == 0) {
    int error = halide_pipeline((halide_buffer_t *)&halide_buffer_in,
                                (halide_buffer_t *)&halide_buffer_in);
  } else {
    halide_slave_core();
  }
  mempool_stop_benchmark();

  // mempool_barrier(num_cores);
#ifdef VERBOSE
  if (core_id == 0) {
    // Print the result
    printf("Histogram Equalization finished with exit code %d\n", error);
    // for (int y = 0; y < buffer_dim_out[1].extent; ++y) {
    //   for (int x = 0; x < buffer_dim_out[0].extent; ++x) {
    for (int y = 0; y < 16; ++y) {
      for (int x = 0; x < 16; ++x) {
        uint8_t val =
            ((uint8_t *)halide_buffer_out.host)[x * buffer_dim_out[0].stride +
                                                y * buffer_dim_out[1].stride];
        printf("%3d ", val);
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
    // Initialize L1 Interleaved Heap Allocator
    extern int32_t __heap_start, __heap_end;
    uint32_t heap_size = (uint32_t)(&__heap_end - &__heap_start);
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);
    // alloc_dump(get_alloc_l1());
  }

  uint8_t const A_a = 1;
  uint8_t const A_b = 4;
  uint8_t const A_c = 32;

  // Initialize Matrices
  mempool_start_benchmark();

  init_img(in, img_width, img_height, A_a, A_b, A_c, core_id, num_cores);

  // Initialized --> Start calculating (implicit barrier at start)
  mempool_start_benchmark();
  error = halide_histogram_equalization(core_id, num_cores);

  return error;
}
