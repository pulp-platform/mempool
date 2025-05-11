// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

/* Dynamic memory allocation based on linked list of free blocks with
 * first-fit search and coalescing with next and previous block
 */

#ifndef _ALLOC_H_
#define _ALLOC_H_

#include "encoding.h"
#include "printf.h"
#include <stddef.h>
#include <stdint.h>

// Free memory block
typedef struct alloc_block_s {
  uint32_t size;
  struct alloc_block_s *next;
} alloc_block_t;

// Allocator
typedef struct {
  alloc_block_t *first_block;
} alloc_t;


// Initialization
void alloc_init(alloc_t *alloc, void *base, const uint32_t size);

// Malloc in L1 memory
void *simple_malloc(const uint32_t size);

void *simple_aligned_malloc(const uint32_t size);

// Dynamic heap allocation with Canary Chain
void *partition_malloc(alloc_t *alloc, const uint32_t size, const uint32_t allocated_size);

// Malloc with specified allocator
void *domain_malloc(alloc_t *alloc, const uint32_t size);

// Free in L1 memory
void simple_free(void *const ptr);

// Free dynamic heap allocation with Canary chain
void partition_free(alloc_t *alloc, void *const ptr);

// Free with specified allocator
void domain_free(alloc_t *alloc, void *const ptr);

// Print out linked list of free blocks
void alloc_dump(alloc_t *alloc);
void canary_dump(void);
// Get allocator for L1 interleaved heap memory
alloc_t *get_alloc_l1();

// Get allocator for L1 local sequential heap memory
alloc_t *get_alloc_tile(const uint32_t tile_id);

// ----- Dynamic Heap Allocator ----- //
extern alloc_t* dynamic_heap_alloc;
void init_dynamic_heap_alloc(uint32_t num_partition);
void free_dynamic_heap_alloc(void);
alloc_t *get_dynamic_heap_alloc(const uint32_t part_id);

#endif
