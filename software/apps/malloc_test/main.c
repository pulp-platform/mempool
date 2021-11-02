// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

extern int32_t __heap_start, __heap_end;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Test
  if (core_id == 0) {
    printf("Initialize\n");

    // Initialize malloc
    uint32_t heap_size = (uint32_t)(&__heap_end - &__heap_start);
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);

    // ------------------------------------------------------------------------
    // Basic Tests
    // ------------------------------------------------------------------------

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Malloc uint32_t array of size 16 (40 bytes)
    uint32_t array_size = 16;
    uint32_t *array = (uint32_t *)simple_malloc(array_size * 4);
    printf("Allocated array at %08X with size %u\n", array, array_size);

    // Malloc uint32_t array of size 32 (40 bytes)
    uint32_t other_array_size = 32;
    uint32_t *other_array = (uint32_t *)simple_malloc(other_array_size * 4);
    printf("Allocated array at %08X with size %u\n", other_array,
           other_array_size);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Test array
    for (uint32_t i = 0; i < 16; ++i) {
      array[i] = i;
    }
    for (uint32_t i = 0; i < 16; ++i) {
      printf("At %08X value is %02u\n", &array[i], array[i]);
    }

    // Free array
    simple_free(array);
    printf("Freed array at %08X with size %u\n", array, array_size);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // Free other array
    simple_free(other_array);
    printf("Freed array at %08X with size %u\n", other_array, other_array_size);

    // Print out allocator
    alloc_dump(get_alloc_l1());

    // ------------------------------------------------------------------------
    // Advanced Tests
    // ------------------------------------------------------------------------

    // Test malloc in the middle
    printf("Test malloc in the middle:\n");
    printf("Allocate A B C then free B and stepwise allocate it again\n");
    alloc_dump(get_alloc_l1());
    uint32_t *a1 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *b1 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *c1 = (uint32_t *)simple_malloc(15 * 4);
    alloc_dump(get_alloc_l1());
    simple_free(b1);
    alloc_dump(get_alloc_l1());
    uint32_t *b1_part1 = (uint32_t *)simple_malloc(7 * 4);
    alloc_dump(get_alloc_l1());
    uint32_t *b1_part2 = (uint32_t *)simple_malloc(7 * 4);
    alloc_dump(get_alloc_l1());
    simple_free(a1);
    simple_free(c1);
    simple_free(b1_part1);
    simple_free(b1_part2);

    // Test critical malloc
    printf("Test critical malloc:\n");
    printf("Allocate A B C then free B and almost fully allocate it again\n");
    alloc_dump(get_alloc_l1());
    uint32_t *a3 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *b3 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *c3 = (uint32_t *)simple_malloc(15 * 4);
    alloc_dump(get_alloc_l1());
    simple_free(b3);
    alloc_dump(get_alloc_l1());
    uint32_t *b3_part1 = (uint32_t *)simple_malloc(13 * 4);
    alloc_dump(get_alloc_l1());
    simple_free(a3);
    simple_free(c3);
    simple_free(b3_part1);

    // Test coalescing
    printf("Test coalescing:\n");
    printf("Allocate A B C then free A, C and finally B\n");
    alloc_dump(get_alloc_l1());
    uint32_t *a2 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *b2 = (uint32_t *)simple_malloc(15 * 4);
    uint32_t *c2 = (uint32_t *)simple_malloc(15 * 4);
    alloc_dump(get_alloc_l1());
    simple_free(a2);
    alloc_dump(get_alloc_l1());
    simple_free(c2);
    alloc_dump(get_alloc_l1());
    simple_free(b2);
    alloc_dump(get_alloc_l1());
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
