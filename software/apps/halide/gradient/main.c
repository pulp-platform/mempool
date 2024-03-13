// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * This example shows how to use Halide on the MemPool system. Specifically, a
 * Halide pipeline is compiled to take two input arguments and return an image
 * in the output buffer. This example shows how to configure the Halide pipeline
 * and the C buffer to be compatible.
 */

#include "encoding.h"
#include "halide_pipeline.riscv.h"
#include "halide_runtime.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <stdint.h>
#include <string.h>

int main() {
  if (mempool_get_core_id() == 0) {
    // Specify a two-dimensional buffer
    halide_dimension_t buffer_dim[2];
    // Fill both dimensions' parameters
    buffer_dim[0].min = 0;
    buffer_dim[0].extent = 15;
    buffer_dim[0].stride = 1;
    buffer_dim[0].flags = 0;
    buffer_dim[1].min = 0;
    buffer_dim[1].extent = 21;
    buffer_dim[1].stride = buffer_dim[0].extent;
    buffer_dim[1].flags = 0;

    // Specify the type of data in the buffer
    struct halide_type_t buffer_type;
    buffer_type.code = halide_type_uint;
    buffer_type.bits = 8;
    buffer_type.lanes = 1;

    // Allocate the buffer and the structure to hold the buffer
    uint8_t buffer[buffer_dim[0].extent * buffer_dim[1].extent];

    // Assign all parameters to the buffer structure
    halide_buffer_t output;
    output.device = 0;
    output.device_interface = NULL;
    output.host = buffer;
    output.flags = 1;
    output.type = buffer_type;
    output.dimensions = 2;
    output.dim = buffer_dim;
    output.padding = 0;

    // Set arguments:
    unsigned center_x = 7;
    unsigned center_y = 7;

    // Call the Halide pipeline
    printf("Start calculation around x=%d, y=%d\n", center_x, center_y);
    int error = gradient(center_x, center_y, &output);

    // Print the result
    printf("Gradient finished with exit code %d\n", error);
    for (int y = 0; y < buffer_dim[1].extent; ++y) {
      for (int x = 0; x < buffer_dim[0].extent; ++x) {
        uint8_t val =
            (output.host)[x * buffer_dim[0].stride + y * buffer_dim[1].stride];
        printf("%2x ", val);
      }
      printf("\n");
    }

    wake_up((uint32_t)-1);
  }
  mempool_wfi();

  return 0;
}
