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

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "alloc.h"

extern int32_t __heap_start, __heap_end;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // Test
  if (core_id == 0) {
    printf("Initialize\n");

    // Initialize malloc
    uint32_t heap_size = (uint32_t)(&__heap_end - &__heap_start);
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Malloc uint32_t array of size 16 (40 bytes)
    uint32_t *array = (uint32_t *)simple_malloc(16 * 4);
    printf("Allocated array at %8X\n", array);

    // Malloc uint32_t array of size 32 (40 bytes)
    uint32_t *other_array = (uint32_t *)simple_malloc(32 * 4);
    printf("Allocated array at %8X\n", other_array);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Test array
    for (uint32_t i = 0; i < 16; ++i) {
      array[i] = i;
    }
    for (uint32_t i = 0; i < 16; ++i) {
      printf("At %8X value is %8X\n", &array[i], array[i]);
    }

    // Free array
    simple_free(array);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Free other array
    simple_free(other_array);

    // Print out allocator
    alloc_dump(get_alloc_l1());
  }

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);
  return 0;
}
