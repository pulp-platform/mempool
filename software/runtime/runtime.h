// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
//         Matheus Cavalcante, ETH Zurich

#pragma once
#include "alloc.h"
#include "encoding.h"
#include <stddef.h>
#include <stdint.h>

#define NUM_BANKS_PER_TILE NUM_CORES_PER_TILE *BANKING_FACTOR

extern char l1_alloc_base;
extern uint32_t atomic_barrier;
extern volatile uint32_t wake_up_reg;
extern volatile uint32_t wake_up_group_reg;

extern volatile uint32_t wake_up_tile_g0_reg;
extern volatile uint32_t wake_up_tile_g1_reg;
extern volatile uint32_t wake_up_tile_g2_reg;
extern volatile uint32_t wake_up_tile_g3_reg;
extern volatile uint32_t wake_up_tile_g4_reg;
extern volatile uint32_t wake_up_tile_g5_reg;
extern volatile uint32_t wake_up_tile_g6_reg;
extern volatile uint32_t wake_up_tile_g7_reg;

typedef uint32_t mempool_id_t;
typedef uint32_t mempool_timer_t;

/// Obtain the number of cores in the current cluster.
static inline mempool_id_t mempool_get_core_count() { return NUM_CORES; }

/// Obtain the ID of the current core.
static inline mempool_id_t mempool_get_core_id() {
  mempool_id_t r;
  asm volatile("csrr %0, mhartid" : "=r"(r));
  return r;
}

/// Obtain the number of tiles in the current cluster.
static inline uint32_t mempool_get_tile_count() {
  return NUM_CORES / NUM_CORES_PER_TILE;
}

/// Obtain the ID of the tile the current core is in.
static inline uint32_t mempool_get_tile_id() {
  return mempool_get_core_id() / NUM_CORES_PER_TILE;
}

/// Obtain the number of groups in the current cluster.
static inline uint32_t mempool_get_group_count() { return NUM_GROUPS; }

/// Obtain the ID of the group the current core is in.
static inline uint32_t mempool_get_group_id() {
  return mempool_get_core_id() / (NUM_CORES / NUM_GROUPS);
}

/// Obtain the number of cores per tile in the current cluster
static inline uint32_t mempool_get_core_count_per_tile() {
  return NUM_CORES_PER_TILE;
}

/// Obtain the number of cores per group in the current cluster
static inline uint32_t mempool_get_core_count_per_group() {
  return NUM_CORES / NUM_GROUPS;
}

/// Initialization
static inline void mempool_init(const uint32_t core_id) {
  if (core_id == 0) {
    // Initialize L1 Interleaved Heap Allocator
    extern uint32_t __heap_start, __heap_end;
    uint32_t heap_size = (uint32_t)&__heap_end - (uint32_t)&__heap_start;
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);

    // Initialize L1 Sequential Heap Allocator per Tile
    extern uint32_t __seq_start;
    // The stack is in the sequential region
    uint32_t seq_heap_offset = NUM_CORES_PER_TILE * STACK_SIZE;
    // preceded by the queues (XQUEUE_SIZE in words)
    seq_heap_offset += NUM_BANKS_PER_TILE * XQUEUE_SIZE * sizeof(uint32_t);
    // The total sequential memory per tile in bytes
    uint32_t seq_total_size = NUM_CORES_PER_TILE * SEQ_MEM_SIZE;
    // The base is the start address + the offset due to the queues and stack
    uint32_t seq_heap_base = (uint32_t)&__seq_start + seq_heap_offset;
    uint32_t seq_heap_size = seq_total_size - seq_heap_offset;
    uint32_t num_tiles = mempool_get_tile_count();
    for (uint32_t tile_id = 0; tile_id < num_tiles; ++tile_id) {
      alloc_t *tile_allocator = get_alloc_tile(tile_id);
      alloc_init(tile_allocator, (uint32_t *)seq_heap_base, seq_heap_size);
      seq_heap_base += seq_total_size;
    }
  }
}

/// Reset a monotonically increasing cycle count.
static inline void mempool_start_benchmark() {
  asm volatile("" ::: "memory");
  write_csr(trace, 1);
  asm volatile("" ::: "memory");
}

/// Obtain a monotonically increasing cycle count.
static inline void mempool_stop_benchmark() {
  asm volatile("" ::: "memory");
  write_csr(trace, 0);
  asm volatile("" ::: "memory");
}

/// Obtain a monotonically increasing cycle count.
static inline mempool_timer_t mempool_get_timer() { return read_csr(mcycle); }

/// Busy loop for waiting
static inline void mempool_wait(uint32_t cycles) {
  asm volatile("1: \n\t"
               "addi %[counter], %[counter], -2 \n\t"
               "bgtz %[counter], 1b \n\t"
               : [counter] "+&r"(cycles)
               :
               : "memory");
}

static inline void mempool_wfi() { asm volatile("wfi"); }

// Wake up core with given core_id by writing in the wake up control register.
// If core_id equals -1, wake up all cores.
static inline void wake_up(uint32_t core_id) { wake_up_reg = core_id; }
static inline void wake_up_all() { wake_up((uint32_t)-1); }
static inline void wake_up_group(uint32_t group_mask) {
  wake_up_group_reg = group_mask;
}
static inline void wake_up_all_group() { wake_up_group((uint32_t)-1); }

static inline void wake_up_tile(uint32_t group_id, uint32_t tile_mask) {

  switch (group_id) {
  case 0:
    wake_up_tile_g0_reg = tile_mask;
    break;
  case 1:
    wake_up_tile_g1_reg = tile_mask;
    break;
  case 2:
    wake_up_tile_g2_reg = tile_mask;
    break;
  case 3:
    wake_up_tile_g3_reg = tile_mask;
    break;
  case 4:
    wake_up_tile_g4_reg = tile_mask;
    break;
  case 5:
    wake_up_tile_g5_reg = tile_mask;
    break;
  case 6:
    wake_up_tile_g6_reg = tile_mask;
    break;
  case 7:
    wake_up_tile_g7_reg = tile_mask;
    break;
  default:
    wake_up_tile_g0_reg = tile_mask;
    break;
  }
}

// Dump a value via CSR
// This is only supported in simulation and an experimental feature. All writes
// to unimplemented CSR registers will be dumped by Snitch. This can be
// exploited to quickly print measurement values from all cores simultaneously
// without the hassle of printf. To specify multiple metrics, different CSRs can
// be used.
// The macro will define a function that will then always print via the same
// CSR. E.g., `dump(errors, 8)` will define a function with the following
// signature: `dump_errors(uint32_t val)`, which will print the given value via
// the 8th register.
// Alternatively, the `write_csr(reg, val)` macro can be used directly.
#define dump(name, reg)                                                        \
  static                                                                       \
      __attribute__((always_inline)) inline void dump_##name(uint32_t val) {   \
    asm volatile("csrw " #reg ", %0" ::"rK"(val));                             \
  }
