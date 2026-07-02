// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Authors: Bowen Wang    <bowwang@iis.ee.ethz.ch>
//          Gua Hao Khov, ETH Zurich

/*
Dynamic memory allocation based on linked list of free memory blocks
*/

#ifndef _FLEX_ALLOC_H_
#define _FLEX_ALLOC_H_

#include <stdint.h>
#include "flex_printf.h"
#include "flex_cluster_arch.h"

/*
Desc: Free-memory-block indicator
@var: (unit32_t)               size -- capacity of the free memory block (in bytes)
@var: (struct alloc_block_s *) next -- pointer to the next free memory block
*/
typedef struct alloc_block_s {
  uint32_t size;
  struct alloc_block_s *next;
} alloc_block_t;

/*
Desc: Allocator data structure
@var: (alloc_block_t *) first block -- pointer to the first free memory block 
*/
typedef struct {
  alloc_block_t *first_block;
} alloc_t;


/********************
*  Initialization   *
********************/

// Initialize the first free-memory-block indicator, and set up the pointer in the allocator
void flex_cluster_alloc_init(alloc_t *alloc, void *base, const uint32_t size);

/***************
*  Allocation  *
***************/

// Memory alllocation with programmer-specified allocator
void *domain_malloc(alloc_t *alloc, const uint32_t size);

// Memory allocation with default l1 heap allocator
void *flex_l1_malloc(const uint32_t size);
void *flex_hbm_malloc(const uint32_t size);


/******************
*  De-allocation  *
******************/

// De-allocation with programmer-specified allocator
void domain_free(alloc_t *alloc, void *const ptr);

// De-allocation with default l1 heap allocator
void flex_l1_free(void *const ptr);
void flex_hbm_free(void *const ptr);

/*********************
*  Helper functions  *
*********************/

// Return the address of the default l1 heap allocator
alloc_t *flex_get_allocator_l1();
alloc_t *flex_get_allocator_hbm();

// [debug] print all free-memory-blocks in l1 heap
void flex_dump_heap();



/********************
*  Implementations  *
********************/

// Block Alignment
#define MIN_BLOCK_SIZE (uint32_t)sizeof(alloc_block_t)

// Alignment functions (size must be a power of 2)
#define ALIGN_UP(addr, size) ((addr + size - 1) & ~(size - 1))
#define ALIGN_DOWN(addr, size) (addr & ~(size - 1))

// Allocator
// TODO: currently placed at a selected address
// bowwang: we can also pass this info from config file
// #define ALLOC_L1 (0x00000000)

// volatile alloc_t * alloc_l1 = (alloc_t *) 0x00000008;
// volatile alloc_t * alloc_l1 = (alloc_t *) ALLOC_L1;
volatile alloc_t alloc_l1 __attribute__((section(".l1_prio")));

// bowwng: allocator for HBM
volatile alloc_t alloc_hbm __attribute__((section(".hbm_prio")));


/*
 Canary System based on LSBs of block pointer   
 |     size     |  canary  |                    
 |    24-bit    |   8-bit  |                    
*/

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



/********************
*  Initialization   *
********************/

void flex_cluster_alloc_init(alloc_t *alloc, void *base, const uint32_t size) {
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
  return;
}



/***********************
*  Memory Allocation   *
***********************/

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
  // Calculate actually required block size
  uint32_t data_size = size + sizeof(uint32_t); // add size/metadata
  uint32_t block_size = ALIGN_UP(data_size, MIN_BLOCK_SIZE); // add alignment

  // 32-bit metadata = 8-bit canary + 24-bit size
  // i.e. max allowed block_size == (2^24 - 1) bytes
  if (block_size >= (1 << (sizeof(uint32_t) * 8 - sizeof(uint8_t) * 8))) {
    printf("Memory allocator: Requested memory exceeds max block size\n");
    return NULL;
  }

  // Allocate memory
  void *block_ptr = allocate_memory(alloc, block_size);
  if (!block_ptr) {
    printf("Memory allocator: No large enough block found (%d)\n", block_size);
    return NULL;
  }

  // Store canary and size into first four bytes
  *((uint32_t *)block_ptr) = canary_encode(block_ptr, block_size);

  // Return data pointer
  void *data_ptr = (void *)((uint32_t *)block_ptr + 1);
  return data_ptr;
}


void *flex_l1_malloc(const uint32_t size) {
  void *addr;
  addr = domain_malloc(&alloc_l1, size);
  return addr;
}

void *flex_hbm_malloc(const uint32_t size) {
  void *addr;
  addr = domain_malloc(&alloc_hbm, size);
  return addr;
}




/*******************
*  De-allocation   *
*******************/

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

void flex_l1_free(void *const ptr)  { domain_free(&alloc_l1, ptr); }
void flex_hbm_free(void *const ptr) { domain_free(&alloc_hbm, ptr); }


/**********************
*  Helper functions   *
**********************/

alloc_t *flex_get_allocator_l1() { return &alloc_l1; }
alloc_t *flex_get_allocator_hbm() { return &alloc_hbm; }


void flex_dump_heap(){
  // access the first free-memory-block indicator
  alloc_block_t *curr = (&alloc_l1)->first_block;
  uint32_t block_id = 0; // for printing

  printf("Memory allocator: Free-memory-block dump\n");
  while (curr) {
  	printf("[block_id %d] addr: 0x%08x, size (byte): %x\n", block_id, (uint32_t)curr, curr->size);
    curr = curr->next;
    block_id += 1;
  }
  printf("\n");
}

#endif