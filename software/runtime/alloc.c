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

// Minimum block size due to alloc_block_t structure (must be a power of 2)
#define MIN_BLOCK_SIZE (uint32_t)sizeof(alloc_block_t)

// Alignment functions (size must be a power of 2)
#define ALIGN_UP(addr, size) ((addr + size - 1) & ~(size - 1))
#define ALIGN_DOWN(addr, size) (addr & ~(size - 1))

// ----------------------------------------------------------------------------
// Static Variables
// ----------------------------------------------------------------------------

// Allocator for L1 interleaved heap memory
alloc_t alloc_l1;

// Allocators for L1 local sequential heap memory
alloc_t alloc_tile[NUM_CORES / NUM_CORES_PER_TILE];


// ----------------------------------------------------------------------------
// Dynamic Heap Allocator 
// ----------------------------------------------------------------------------
alloc_t* dynamic_heap_alloc = NULL;
void init_dynamic_heap_alloc(uint32_t num_partition){ // how many parts to devide the whole system
  dynamic_heap_alloc = (alloc_t *)simple_malloc(num_partition * sizeof(alloc_t));
}
void free_dynamic_heap_alloc(void){
  simple_free(dynamic_heap_alloc);
}

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

typedef struct canary_chain_s{
  uint32_t                 canary_and_size;
  uint32_t                 *data_address;
  struct canary_chain_s    *next_canary;
} canary_chain_t;

// init as a NULL, assign this pointer when the first canary is allocated
// It is a pointer pointing to the canary chain
// canary_start_t first_canary;
canary_chain_t *first_canary = (canary_chain_t *)0x1000;

// ----------------------------------------------------------------------------
// Initialization
// ----------------------------------------------------------------------------
void alloc_init(alloc_t *alloc, void *base, const uint32_t size) {
  // Create first block at base address aligned up
  uint32_t aligned_base = ALIGN_UP((uint32_t)base, MIN_BLOCK_SIZE);
  // printf("base - %p - aligned_base %p\n", base, (alloc_block_t *)aligned_base);
  alloc_block_t *block_ptr = (alloc_block_t *)aligned_base;

  // Calculate block size aligned down
  uint32_t block_size = size - ((uint32_t)block_ptr - (uint32_t)base);
  block_size = ALIGN_DOWN(block_size, MIN_BLOCK_SIZE);

  // printf("block_ptr: %p, block_ptr->size: %p, block_ptr->next: %p\n", block_ptr, &(block_ptr->size), &(block_ptr->next));

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

// ------ Function to calculate the aligned size ------ //
static uint32_t calc_aligned_size (uint32_t* addr, const uint32_t allocated_size) {
  // interpret the addr
  uint32_t tmp = allocated_size;
  uint32_t log = 0; // log2 of 0 is undefined, handled as special case if needed
  while (tmp >>= 1) { // Shift right until value is 0
      ++log;
  }
  uint32_t mask = (uint32_t)(( 1 << log )-1);
  uint32_t row_id, tile_id, offset;
  offset  =  ((uint32_t)addr)       & 0x7F;
  tile_id =  ((uint32_t)addr >> 7 ) & 0x7F;
  row_id  =  ((uint32_t)addr >> 14) & 0xFF;
  row_id &= mask;

  uint32_t shift_size=0;
  if ( (offset==0) && (row_id==0) && (tile_id==0) ){
    shift_size = 0;
  }
  else{
    uint32_t aligned_boundary = 4096*4*allocated_size;
    uint32_t modified_curr    = (row_id<<14) | (tile_id<<7) | offset;
    shift_size = aligned_boundary - modified_curr;
  }

  return shift_size;
}
// ------ Parameters ------ //
// size:           Size of the data block need to be allocated
// allocated_size: How many rows the current partition scheme occupied
static void *allocate_memory_aligned(alloc_t *alloc, const uint32_t size, const uint32_t allocated_size) {
  // Get first block of linked list of free blocks
  alloc_block_t *curr = alloc->first_block;
  alloc_block_t *prev = 0;

  // Search first block large enough in linked list
  // 1. calculate the size aligned to the partition boundary
  uint32_t shift_size = 0;
  shift_size = calc_aligned_size( (uint32_t*)curr, allocated_size);
  uint32_t aligned_size = size + shift_size;

  // while (curr && (curr->size < size)) {
  while (curr && (curr->size < aligned_size)) {
    prev = curr;
    curr = curr->next;
    shift_size = calc_aligned_size( (uint32_t*)curr, allocated_size);
    aligned_size = size + shift_size;
  }
  printf("Dynamic Allocator >> size [%d] --- shift size [%d] --- aligned size [%d] \n", size, shift_size, aligned_size);

  if (curr) {
    // Update allocator
    if (size == aligned_size){
      // address is already aligned to the partition boundary
      printf("Dynamic Allocator >> No alignment needed\n");
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
    }
    else{
      printf("Dynamic Allocator >> Alignment needed\n");
      if (curr->size == aligned_size) {
        // Special case: Whole block taken, first part of the block is still empty
        // store the curr info in tmp
        // uint32_t tmp_size = curr->size;
        struct alloc_block_s *tmp_next = curr->next;
        alloc_block_t *shift_block = (alloc_block_t *)((char *)curr);
        shift_block->size = shift_size;
        shift_block->next = tmp_next;
        if (prev) {
          prev->next = shift_block;
        } else {
          alloc->first_block = shift_block;
        }
      } 
      else{
        // Regular case: Split off block
        alloc_block_t *new_block = (alloc_block_t *)((char *)curr + aligned_size);
        new_block->size = curr->size - aligned_size;
        new_block->next = curr->next;

        alloc_block_t *shift_block = (alloc_block_t *)((char *)curr);
        shift_block->size = shift_size;
        shift_block->next = new_block;
        if (prev) {
          prev->next = shift_block;
        } else {
          alloc->first_block = shift_block;
        }
      }
    }

    // Return block pointer
    return (void *)((char *)curr+shift_size);
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

void *simple_malloc(const uint32_t size) {
  return domain_malloc(&alloc_l1, size);
}

// ------ Allocate a space aligned with L1 boundary ------ //
static uint32_t calc_aligned_l1_size (uint32_t* addr) {
  uint32_t shift_size = 0;
  uint32_t l1_aligned_mask = 0x3fff;
  uint32_t masked_addr     = (uint32_t)addr & l1_aligned_mask;
  if (masked_addr==0x3ffc){
    shift_size = 0;
  }
  else{
    shift_size = 0x3ffc - masked_addr;
  }
  return shift_size;
}

// Input size is block size: [data_size + meta_size]
static void *allocate_memory_l1_aligned(alloc_t *alloc, const uint32_t size) {
  // Get first block of linked list of free blocks
  alloc_block_t *curr = alloc->first_block;
  alloc_block_t *prev = 0;

  uint32_t shift_size = 0;
  shift_size = calc_aligned_l1_size( (uint32_t*)curr);
  uint32_t aligned_size = size + shift_size;

  // Search first block large enough in linked list
  while (curr && (curr->size < aligned_size)) {
    prev = curr;
    curr = curr->next;

    shift_size = calc_aligned_l1_size( (uint32_t*)curr);
    aligned_size = size + shift_size;
  }

  if (curr) {
    // Update allocator
    if (shift_size==0){
      printf("[L1 Alloc] No Alignment.\n");
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
    }
    else{
      printf("[L1 Alloc] Alignment Needed.\n");
      if (curr->size == aligned_size) {
        // Special case: Whole block taken, first part of the block is still empty
        // store the curr info in tmp
        // uint32_t tmp_size = curr->size;
        struct alloc_block_s *tmp_next = curr->next;
        alloc_block_t *shift_block = (alloc_block_t *)((char *)curr);
        shift_block->size = shift_size;
        shift_block->next = tmp_next;
        if (prev) {
          prev->next = shift_block;
        } else {
          alloc->first_block = shift_block;
        }
      } 
      else{
        // Regular case: Split off block
        alloc_block_t *new_block = (alloc_block_t *)((char *)curr + aligned_size);
        new_block->size = curr->size - aligned_size;
        new_block->next = curr->next;

        alloc_block_t *shift_block = (alloc_block_t *)((char *)curr);
        shift_block->size = shift_size;
        shift_block->next = new_block;
        if (prev) {
          prev->next = shift_block;
        } else {
          alloc->first_block = shift_block;
        }
      }
    }

    // Return block pointer
    return (void *)((char *)curr+shift_size);
  } else {
    // There is no free block large enough
    return NULL;
  }
}

void *domain_malloc_aligned(alloc_t *alloc, const uint32_t size) {
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
  void *block_ptr = allocate_memory_l1_aligned(alloc, block_size);
  if (!block_ptr) {
    printf("Memory allocator: No large enough block found (%d)\n", block_size);
    return NULL;
  }

  // Store canary and size into first four bytes
  *((uint32_t *)block_ptr) = canary_encode(block_ptr, block_size);

  // Return data pointer
  void *data_ptr = (void *)((uint32_t *)block_ptr + 1);
  printf("[Aligned malloc] addr: %p - size: %d\n", data_ptr, size);
  return data_ptr;
}

void *simple_aligned_malloc(const uint32_t size){
  return domain_malloc_aligned(&alloc_l1, size);
}

// ------ This function allocate data in Sequential Heap region ------ //
// Canary system is stored in a seperate linked list
// void *partition_malloc(alloc_t *alloc, const uint32_t size){
void *partition_malloc(alloc_t *alloc, const uint32_t size, const uint32_t allocated_size){
  uint32_t data_size = size;
  uint32_t block_size = ALIGN_UP(data_size, MIN_BLOCK_SIZE); // add alignment

  // Check if exceed maximum allowed size
  if (block_size >= (1 << (sizeof(uint32_t) * 8 - sizeof(uint8_t) * 8))) {
    printf("Memory allocator: Requested memory exceeds max block size\n");
    return NULL;
  }

  // allocate 
  void *block_ptr = NULL;
  if (allocated_size<2){
    block_ptr = allocate_memory(alloc, block_size);
  }
  else{
    block_ptr = allocate_memory_aligned(alloc, block_size, allocated_size);
  }
  // void *block_ptr = allocate_memory(alloc, block_size);
  // void *block_ptr = allocate_memory_aligned(alloc, block_size, allocated_size);
  if (!block_ptr) {
    printf("Memory allocator: No large enough block found (%d)\n", block_size);
    return NULL;
  }

  // Allocate a region in L1 heap for canary
  // printf("p1\n");
  canary_chain_t *canary =  (canary_chain_t *)simple_malloc(sizeof(canary_chain_t));
  // printf("p2\n");
  // Init the canary
  canary->data_address = (uint32_t *)block_ptr;
  canary->canary_and_size = canary_encode(block_ptr, block_size);
  canary->next_canary = NULL;

  // link the canary into the list
  // canary_chain_t *curr = first_canary->first_block;
  canary_chain_t *curr = first_canary;
  canary_chain_t *prev = 0;
  

  // Fit the canary into the chain, depending on data_address
  // | prev |  ------> | canary | ------> | curr |
  uint32_t *data_addr = 0;
  if (curr != (canary_chain_t *)0x1000){
    // only access struct when init
    data_addr = curr->data_address;
  }

  while((curr!=(canary_chain_t *)0x1000) && (curr!=NULL) && ((uint32_t *)data_addr < (uint32_t *)block_ptr)){
    prev = curr;
    // data_addr = curr->data_address;
    curr = curr->next_canary;
    if (curr!=NULL){
      data_addr = curr->data_address;
    }
    // data_addr = curr->data_address;
  }

  // printf("post: %p - %p \n", curr, prev);
  if ((curr==(canary_chain_t *)0x1000) && !prev) {
    // special case: first canary block
    first_canary = canary;
    printf("| First | ------> [ New ]\n");
    // printf("first_canary: %p\n", first_canary);
  }
  else{
    if (!curr){
      // reach to the last of the chain
      // | prev | ------> | canary | ------> NULL
      prev->next_canary   = canary;
      canary->next_canary = NULL;
      printf("| Other | ------> [ New ] ------> NULL\n");
    }
    else if (!prev){
      // canary need to insert at the beginning of the chain
      // first_canary ------> | canary | ------> | curr |
      first_canary = canary;
      canary->next_canary = curr;
      printf("| First | ------> [ New ] ------> | Other |\n");
    }
    else{
      // normal case
      // | prev |  ------> | canary | ------> | curr |
      canary->next_canary = prev->next_canary;
      prev->next_canary   = canary;
      printf("| Other | ------> [ New ] ------> | Other |\n");
    }

  }
  // return the block pointer directly
  // printf("%p\n", block_ptr);
  return block_ptr;
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

void partition_free(alloc_t *alloc, void *const ptr){
  // block pointer is the input pointer
  void *block_ptr = ptr;

  canary_and_size_t canary_and_size = (canary_and_size_t){.canary = 0, .size = 0};
  // find the canary block in the chain
  canary_chain_t *curr = first_canary;
  canary_chain_t *prev = 0;

  // While loop suppose to stop when curr->data_address == block_ptr
  // | prev |  ------>  | curr |
  uint32_t *data_addr = 0;
  if (curr){
    data_addr = curr->data_address;
  }
  printf("data_addr - %p - block_ptr - %p - curr->data_address - %p \n", data_addr, block_ptr, curr->data_address);
  while((curr!=(canary_chain_t *)0x1000) && (curr!=NULL) && (data_addr < (uint32_t *)block_ptr)){
    prev = curr;
    // data_addr = curr->data_address;
    curr = curr->next_canary;
    if(curr!=NULL){
      data_addr = curr->data_address;
    }
  }

  if ((curr==(canary_chain_t *)0x1000) && !prev){
    // nothing in the chain
    printf("CANARY: Empty canary chain!\n");
  }
  else if (!curr){
    // reach to the end of the chain
    printf("CANARY: Chain depleted. No info found for %p\n", block_ptr);
  }
  else if (curr->data_address != block_ptr){
    // no information for the current free
    printf("CANARY: Unmatch! %p - %p\n", curr->data_address, block_ptr);
  }
  else if (!prev){
    // normal case 1: curr is the first canary
    // first_canary ------> | curr | ------> next
    canary_and_size = canary_decode(curr->canary_and_size);
    if (curr->next_canary == NULL){
      first_canary = (canary_chain_t *)0x1000;
    }
    else{
      first_canary = curr->next_canary;
    }

    simple_free((void *)curr);
  }
  else{
    // normal case 2: relink the chain, free the curr canary
    // | prev | ------> | curr | ------> something
    canary_and_size = canary_decode(curr->canary_and_size);
    prev->next_canary = curr->next_canary;
    simple_free((void *)curr);
  }

  // Check for memory overflow
  if (canary_and_size.canary != canary(block_ptr)) {
    if (!canary_and_size.canary) {
      printf("Empty canary.\n");
    }
    printf("Memory Overflow at %p\n", block_ptr);
    return;
  }

  // Free memory
  free_memory(alloc, block_ptr, canary_and_size.size);
  
}

// ----------------------------------------------------------------------------
// Debugging Functions
// ----------------------------------------------------------------------------
void alloc_dump(alloc_t *alloc) {
  // Get first block of linked list of free blocks
  alloc_block_t *curr = alloc->first_block;

  printf("Memory Allocator State\n");

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
}

void canary_dump(void){
  printf(" ------ Canary Chain Dump ------ \n");
  canary_chain_t *curr = first_canary;
  if (curr == (canary_chain_t *)0x1000){
    // empty list
    printf("Empty Canary list.\n");
  }
  else{
    uint32_t cnt = 0;
    while(curr!=NULL){
      printf("[%d] - [%p] - [%p] - [%p]\n", cnt, curr, curr->data_address, curr->next_canary);
      cnt += 1;
      curr = curr->next_canary;
    }
  }
  printf(" ------ Canary Dump END ------ \n");
}


// ----------------------------------------------------------------------------
// Get Allocators
// ----------------------------------------------------------------------------
// Get the address of global variable `alloc_l1` 
alloc_t *get_alloc_l1() { return &alloc_l1; }

alloc_t *get_alloc_tile(const uint32_t tile_id) { return &alloc_tile[tile_id]; }

// Dynamic Heap Allocator 
alloc_t *get_dynamic_heap_alloc(const uint32_t part_id) {return &dynamic_heap_alloc[part_id];}