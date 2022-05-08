// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

#include "alloc.h"
#include "printf.h"

// ----------------------------------------------------------------------------
// Block Alignment
// ----------------------------------------------------------------------------
/* Alignment to MIN_BLOCK_SIZE ensures that blocks are always multiples of it,
 * e.g. a split off block is always at least MIN_BLOCK_SIZE large and can thus
 * still fit the alloc_block_t structure (size and *next).
 * Initialization must ensure that the first block is properly aligned!
 * Malloc must ensure to allocate aligned up to next chunk!
 */

// Minimum block size due to alloc_block_t structure
#define MIN_BLOCK_SIZE (uint32_t)8

// Alignment functions
#define ALIGN_UP(addr, size) ((addr + size - 1) & ~(size - 1))
#define ALIGN_DOWN(addr, size) (addr & ~(size - 1))

// ----------------------------------------------------------------------------
// Static Variables
// ----------------------------------------------------------------------------

// Allocator for L1 interleaved heap memory
alloc_t alloc_l1 __attribute__((section(".l2")));

// Allocators for L1 local sequential heap memory
alloc_t alloc_tile[NUM_CORES / 4] __attribute__((section(".l2")));

// ----------------------------------------------------------------------------
// Canary System based on LSBs of block pointer
// ----------------------------------------------------------------------------
typedef struct {
  uint32_t size;
  uint8_t canary;
} canary_and_size_t;

static inline uint8_t canary(const void *const ptr) {
  return (uint32_t)ptr & 0xFF;
}

static inline uint32_t canary_encode(const void *const ptr,
                                     const uint32_t size) {
  return (size << 8) | canary(ptr);
}

static inline canary_and_size_t canary_decode(const uint32_t value) {
  return (canary_and_size_t){.canary = value & 0xFF, .size = value >> 8};
}

// ----------------------------------------------------------------------------
// Initialization
// ----------------------------------------------------------------------------
void alloc_init(alloc_t *alloc, void *base, const uint32_t size) {
  // Create first block at base address aligned up
  uint32_t aligned_base = ALIGN_UP((uint32_t)base, MIN_BLOCK_SIZE);
  alloc_block_t *block_ptr = (alloc_block_t *)aligned_base;

  // Calculate block size aligned down
  uint32_t block_size = size - ((uint32_t)block_ptr - (uint32_t)base);
  block_size = ALIGN_DOWN(block_size, MIN_BLOCK_SIZE);

  // Setup allocator
  block_ptr->size = block_size;
  block_ptr->next = NULL;
  alloc->first_block = block_ptr;
}

// ----------------------------------------------------------------------------
// Allocate Memory
// ----------------------------------------------------------------------------
static void *allocate_memory(alloc_t *alloc, const uint32_t size) {
  // Get first block of linked list of free blocks
  alloc_block_t *curr = alloc->first_block;
  alloc_block_t *prev = 0;

  // Search first block large enough in linked list
  while (curr && (curr->size < size)) {
    prev = curr;
    curr = curr->next;
  }

  if (curr) {
    // Update allocator
    if (curr->size == size) {
      // Special case: Whole block taken
      if (prev) {
        prev->next = curr->next;
      } else {
        alloc->first_block = curr->next;
      }
    } else {
      // Regular case: Split off block
      alloc_block_t *new_block = (alloc_block_t *)((char *)curr + size);
      new_block->size = curr->size - size;
      new_block->next = curr->next;
      if (prev) {
        prev->next = new_block;
      } else {
        alloc->first_block = new_block;
      }
    }

    // Return block pointer
    return (void *)curr;
  } else {
    // There is no free block large enough
    return NULL;
  }
}

void *domain_malloc(alloc_t *alloc, const uint32_t size) {
  // Calculate actual required block size (+ size/metadata + alignment)
  uint32_t data_size = size + 4;
  uint32_t block_size = ALIGN_UP(data_size, MIN_BLOCK_SIZE);

  // Block size must not exceed 24 bits to ensure space for canary
  if (block_size >= (1 << 24)) {
    printf("Memory allocator: Requested memory exceeds max block size\n");
    return NULL;
  }

  // Allocate memory
  void *block_ptr = allocate_memory(alloc, block_size);
  if (!block_ptr) {
    printf("Memory allocator: No large enough block found\n");
    return NULL;
  }

  // Store canary and size into first four bytes
  *((uint32_t *)block_ptr) = canary_encode(block_ptr, block_size);

  // Return data pointer
  void *data_ptr = (void *)((uint32_t *)block_ptr + 1);
  return data_ptr;
}

void *simple_malloc(const uint32_t size) {
  return domain_malloc(&alloc_l1, size);
}

// ----------------------------------------------------------------------------
// Free Memory
// ----------------------------------------------------------------------------
static void free_memory(alloc_t *alloc, void *const ptr, const uint32_t size) {
  alloc_block_t *block_ptr = (alloc_block_t *)ptr;
  // Get first block of linked list of free blocks
  alloc_block_t *next = alloc->first_block;
  alloc_block_t *prev = 0;

  // Find position in linked list of free blocks
  while (next && next < block_ptr) {
    prev = next;
    next = next->next;
  }

  // Connect with next block
  if (((char *)block_ptr + size) == (char *)next) {
    // Special case: Coalesce with adjacent next block
    block_ptr->size = size + next->size;
    block_ptr->next = next->next;
  } else {
    // Regular case: Link to next block
    block_ptr->size = size;
    block_ptr->next = next;
  }

  if (prev) {
    // Connect with previous block
    if (((char *)prev + prev->size) == (char *)block_ptr) {
      // Special case: Coalesce with adjacent previous block
      prev->size += block_ptr->size;
      prev->next = block_ptr->next;
    } else {
      // Regular case: Link from previous block
      prev->next = block_ptr;
    }
  } else {
    alloc->first_block = block_ptr;
  }
}

void domain_free(alloc_t *alloc, void *const ptr) {
  // Get block pointer from data pointer
  void *block_ptr = (void *)((uint32_t *)ptr - 1);

  // Retrieve canary and size
  const canary_and_size_t canary_and_size =
      canary_decode(*(const uint32_t *)block_ptr);

  // Check for memory overflow
  if (canary_and_size.canary != canary(block_ptr)) {
    printf("Memory Overflow at %p\n", block_ptr);
    return;
  }

  // Free memory
  free_memory(alloc, block_ptr, canary_and_size.size);
}

void simple_free(void *const ptr) { domain_free(&alloc_l1, ptr); }

// ----------------------------------------------------------------------------
// Debugging Functions
// ----------------------------------------------------------------------------
void alloc_dump(alloc_t *alloc) {
  // Get first block of linked list of free blocks
  alloc_block_t *curr = alloc->first_block;

  printf("======== Memory Allocator State ========\n");

  // Print out linked list of free blocks
  while (curr) {
    // Print current block
    printf("Free Block at %08X with size %7u\n", (uint32_t)curr, curr->size);

    // Check for self-pointing block
    if (curr->next == curr) {
      printf("Block points to itself! \n");
      break;
    }

    // Go to next block
    curr = curr->next;
  }

  printf("========================================\n");
}

// ----------------------------------------------------------------------------
// Get Allocators
// ----------------------------------------------------------------------------
alloc_t *get_alloc_l1() { return &alloc_l1; }

alloc_t *get_alloc_tile(const uint32_t tile_id) { return &alloc_tile[tile_id]; }
