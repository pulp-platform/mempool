// Copyright 2019 ETH Zurich and University of Bologna.
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

/*
 * This example shows how to use Halide on the MemPool system. Specifically, a
 * Halide pipeline is compiled to take two input arguments and return an image
 * in the output buffer. This example shows how to configure the Halide pipeline
 * and the C buffer to be compatible.
 */

#include "gradient_riscv.h"
#include "rt/rt_api.h"
#include <stdint.h>
#include <stdio.h>

int main() {
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
  void *buffer =
      rt_alloc(RT_ALLOC_CL_DATA,
               buffer_dim[0].extent * buffer_dim[1].extent * sizeof(uint8_t));
  if (buffer == NULL) {
    printf("Buffer could not be allocated\n");
    return 1;
  }

  halide_buffer_t *output = rt_alloc(RT_ALLOC_CL_DATA, sizeof(halide_buffer_t));
  if (output == NULL) {
    printf("Output could not be allocated\n");
    return 1;
  }

  // Assign all parameters to the buffer structure
  output->device = 0;
  output->device_interface = NULL;
  output->host = buffer;
  output->flags = 1;
  output->type = buffer_type;
  output->dimensions = 2;
  output->dim = buffer_dim;
  output->padding = 0;

  // Set arguments:
  unsigned center_x = 7;
  unsigned center_y = 7;

  // Call the Halide pipeline
  printf("Start calculation around x=%d, y=%d\n", center_x, center_y);
  int error = gradient(center_x, center_y, output);

  // Print the result
  printf("Gradient finished with exit code %d\n", error);
  for (int y = 0; y < buffer_dim[1].extent; ++y) {
    for (int x = 0; x < buffer_dim[0].extent; ++x) {
      uint8_t val =
          ((uint8_t *)output
               ->host)[x * buffer_dim[0].stride + y * buffer_dim[1].stride];
      printf("%2x ", val);
    }
    printf("\n");
  }

  return 0;
}
