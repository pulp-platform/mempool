// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Macros
#define UNROLL (4)
#define N (NUM_CORES*UNROLL)

// Prototypes
static inline void power_profile(int32_t *const a);
static inline void power_profile_remote_lw(int32_t *const a, uint32_t remote_tile, uint32_t remote_sub_group, uint32_t remote_group);

// Globals
int32_t block_a[N] __attribute__((aligned(NUM_CORES * 4), section(".l1")));

/* Main */

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);
  for (int i = (int)core_id*UNROLL; i < N; i+=(int)(num_cores*UNROLL)) {
    // UNROLL
    block_a[i+0] = -1111608459 + i * (   52918781);
    block_a[i+1] =  -192269334 + i * (  942963224);
    block_a[i+2] =   600576702 + i * (-1245786405);
    block_a[i+3] =   132428405 + i * (  232792075);
  }

  // normal instr testing
  mempool_barrier(num_cores);
  power_profile(block_a);

  // Remote lw testing
  // Don't use core_0 to avoid lsu conflict with barrier
  mempool_barrier(num_cores);
  uint32_t tile_id = (core_id / NUM_CORES_PER_TILE) % NUM_TILES_PER_SUB_GROUP;
  uint32_t sub_group_id = (core_id / NUM_CORES_PER_SUB_GROUP) % NUM_SUB_GROUPS_PER_GROUP;
  uint32_t group_id =  (core_id / NUM_CORES_PER_GROUP) % NUM_GROUPS;
  uint32_t number_banks_per_sub_group = BANKING_FACTOR * NUM_CORES_PER_SUB_GROUP;
  uint32_t number_banks_per_group = BANKING_FACTOR * NUM_CORES_PER_GROUP;
  uint32_t remote_tile = (core_id * BANKING_FACTOR + NUM_BANKS_PER_TILE) - (tile_id/(NUM_TILES_PER_SUB_GROUP-1)) * number_banks_per_sub_group;
  uint32_t remote_sub_group = (core_id * BANKING_FACTOR + number_banks_per_sub_group) - (sub_group_id/(NUM_SUB_GROUPS_PER_GROUP-1)) * number_banks_per_group;
  uint32_t remote_group = (core_id * BANKING_FACTOR + number_banks_per_group) - (group_id/(NUM_GROUPS-1)) * NUM_CORES * BANKING_FACTOR;
  if ((core_id % 8) == 6) {
    power_profile_remote_lw(block_a, remote_tile, remote_sub_group, remote_group);
  } else {
    mempool_wait(2000);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}

/* Functions */

static inline void power_profile(int32_t *const a) {
  // Who am I?
  uint32_t core_id = mempool_get_core_id();

  // Address to load from are [addr:addr+3]
  volatile int32_t* addr_local  = &a[core_id * (NUM_BANKS_PER_TILE/NUM_CORES_PER_TILE)];

  // Do this loop M times
  int const num_loops = 2;
  int32_t op_a0 =  1763350245;
  int32_t op_a1 =  -473677120;
  int32_t op_a2 = -1893217350;
  int32_t op_a3 =  -915173234;
  int32_t op_a4 =  -715022251;
  int32_t op_a5 =  1755108161;
  int32_t op_a6 =  1629317995;
  int32_t op_a7 = -1694958999;
  int32_t idx = num_loops;
  int32_t im_0 = 0;
  // Temporary registers
  register int32_t op_0;
  register int32_t op_1;
  register int32_t op_2;
  register int32_t op_3;
  register int32_t a0;
  register int32_t a1;
  register int32_t a2;
  register int32_t a3;
  register int32_t a4;
  register int32_t a5;
  register int32_t a6;
  register int32_t a7;
  __asm__ volatile(
      // local lw -> mul -> add -> p.mac
      ".balign 16 \n\t"
      "1: \n\t"
      "lw %[a0],  0(%[a_local]) \n\t"
      "lw %[a1],  4(%[a_local]) \n\t"
      "lw %[a2],  8(%[a_local]) \n\t"
      "lw %[a3], 12(%[a_local]) \n\t"
      "lw %[a4],  0(%[a_local]) \n\t"
      "lw %[a5],  4(%[a_local]) \n\t"
      "lw %[a6],  8(%[a_local]) \n\t"
      "lw %[a7], 12(%[a_local]) \n\t"
      "lw %[a0],  0(%[a_local]) \n\t"
      "lw %[a1],  4(%[a_local]) \n\t"
      "lw %[a2],  8(%[a_local]) \n\t"
      "lw %[a3], 12(%[a_local]) \n\t"
      "lw %[a4],  0(%[a_local]) \n\t"
      "lw %[a5],  4(%[a_local]) \n\t"
      "lw %[a6],  8(%[a_local]) \n\t"
      "lw %[a7], 12(%[a_local]) \n\t"
      "lw %[a0],  0(%[a_local]) \n\t"
      "lw %[a1],  4(%[a_local]) \n\t"
      "lw %[a2],  8(%[a_local]) \n\t"
      "lw %[a3], 12(%[a_local]) \n\t"
      "lw %[a4],  0(%[a_local]) \n\t"
      "lw %[a5],  4(%[a_local]) \n\t"
      "lw %[a6],  8(%[a_local]) \n\t"
      "lw %[a7], 12(%[a_local]) \n\t"
      "lw %[a0],  0(%[a_local]) \n\t"
      "lw %[a1],  4(%[a_local]) \n\t"
      "lw %[a2],  8(%[a_local]) \n\t"
      "lw %[a3], 12(%[a_local]) \n\t"
      "lw %[a4],  0(%[a_local]) \n\t"
      "lw %[a5],  4(%[a_local]) \n\t"
      "lw %[a6],  8(%[a_local]) \n\t"
      "lw %[a7], 12(%[a_local]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 1b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "2: \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 2b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "3: \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 3b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "4: \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "p.mac %[op_0],%[op_a0],%[op_a4] \n\t"
      "p.mac %[op_1],%[op_a1],%[op_a5] \n\t"
      "p.mac %[op_2],%[op_a2],%[op_a6] \n\t"
      "p.mac %[op_3],%[op_a3],%[op_a7] \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 4b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      : [op_0] "=&r"(op_0), [op_1] "=&r"(op_1), [op_2] "=&r"(op_2),
        [op_3] "=&r"(op_3), [a0] "=&r"(a0), [a1] "=&r"(a1), [a2] "=&r"(a2),
        [a3] "=&r"(a3), [a4] "=&r"(a4), [a5] "=&r"(a5), [a6] "=&r"(a6),
        [a7] "=&r"(a7), [idx] "+&r"(idx)
      : [im_0] "r"(im_0), [num_loops] "I"(num_loops), [op_a0] "r"(op_a0),
        [op_a1] "r"(op_a1), [op_a2] "r"(op_a2), [op_a3] "r"(op_a3),
        [op_a4] "r"(op_a4), [op_a5] "r"(op_a5), [op_a6] "r"(op_a6),
        [op_a7] "r"(op_a7), [a_local] "r"(addr_local)
      : "memory");
}


static inline void power_profile_remote_lw(int32_t *const a, uint32_t remote_tile, uint32_t remote_sub_group, uint32_t remote_group) {

  // Address to load from are [addr:addr+3]
  volatile int32_t* addr_remote_tile = &a[remote_tile];
  volatile int32_t* addr_remote_sub_group = &a[remote_sub_group];
  volatile int32_t* addr_remote_group = &a[remote_group];

  // Do this loop M times
  int const num_loops = 2;
  int32_t idx = num_loops;
  int32_t im_0 = 0;
  // Temporary registers
  register int32_t a0;
  register int32_t a1;
  register int32_t a2;
  register int32_t a3;
  register int32_t a4;
  register int32_t a5;
  register int32_t a6;
  register int32_t a7;
  __asm__ volatile(
      // NOP to wait for instruction cache refill
      ".balign 16 \n\t"
      "1: \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 1b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      // remote tile load from same sub-group
      ".balign 16 \n\t"
      "2: \n\t"
      "lw %[a0],  0(%[a_remote_tile]) \n\t"
      "lw %[a1],  4(%[a_remote_tile]) \n\t"
      "lw %[a2],  8(%[a_remote_tile]) \n\t"
      "lw %[a3], 12(%[a_remote_tile]) \n\t"
      "lw %[a4],  0(%[a_remote_tile]) \n\t"
      "lw %[a5],  4(%[a_remote_tile]) \n\t"
      "lw %[a6],  8(%[a_remote_tile]) \n\t"
      "lw %[a7], 12(%[a_remote_tile]) \n\t"
      "lw %[a0],  0(%[a_remote_tile]) \n\t"
      "lw %[a1],  4(%[a_remote_tile]) \n\t"
      "lw %[a2],  8(%[a_remote_tile]) \n\t"
      "lw %[a3], 12(%[a_remote_tile]) \n\t"
      "lw %[a4],  0(%[a_remote_tile]) \n\t"
      "lw %[a5],  4(%[a_remote_tile]) \n\t"
      "lw %[a6],  8(%[a_remote_tile]) \n\t"
      "lw %[a7], 12(%[a_remote_tile]) \n\t"
      "lw %[a0],  0(%[a_remote_tile]) \n\t"
      "lw %[a1],  4(%[a_remote_tile]) \n\t"
      "lw %[a2],  8(%[a_remote_tile]) \n\t"
      "lw %[a3], 12(%[a_remote_tile]) \n\t"
      "lw %[a4],  0(%[a_remote_tile]) \n\t"
      "lw %[a5],  4(%[a_remote_tile]) \n\t"
      "lw %[a6],  8(%[a_remote_tile]) \n\t"
      "lw %[a7], 12(%[a_remote_tile]) \n\t"
      "lw %[a0],  0(%[a_remote_tile]) \n\t"
      "lw %[a1],  4(%[a_remote_tile]) \n\t"
      "lw %[a2],  8(%[a_remote_tile]) \n\t"
      "lw %[a3], 12(%[a_remote_tile]) \n\t"
      "lw %[a4],  0(%[a_remote_tile]) \n\t"
      "lw %[a5],  4(%[a_remote_tile]) \n\t"
      "lw %[a6],  8(%[a_remote_tile]) \n\t"
      "lw %[a7], 12(%[a_remote_tile]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 2b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      // NOP to avoid not resolved instructions
      ".balign 16 \n\t"
      "3: \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 3b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      // remote sub-group load from same group
      ".balign 16 \n\t"
      "4: \n\t"
      "lw %[a0],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a1],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a2],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a3], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a4],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a5],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a6],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a7], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a0],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a1],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a2],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a3], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a4],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a5],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a6],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a7], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a0],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a1],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a2],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a3], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a4],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a5],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a6],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a7], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a0],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a1],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a2],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a3], 12(%[a_remote_sub_group]) \n\t"
      "lw %[a4],  0(%[a_remote_sub_group]) \n\t"
      "lw %[a5],  4(%[a_remote_sub_group]) \n\t"
      "lw %[a6],  8(%[a_remote_sub_group]) \n\t"
      "lw %[a7], 12(%[a_remote_sub_group]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 4b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      // NOP to avoid not resolved instructions
      ".balign 16 \n\t"
      "5: \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "nop \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 5b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      // remote group load
      ".balign 16 \n\t"
      "6: \n\t"
      "lw %[a0],  0(%[a_remote_group]) \n\t"
      "lw %[a1],  4(%[a_remote_group]) \n\t"
      "lw %[a2],  8(%[a_remote_group]) \n\t"
      "lw %[a3], 12(%[a_remote_group]) \n\t"
      "lw %[a4],  0(%[a_remote_group]) \n\t"
      "lw %[a5],  4(%[a_remote_group]) \n\t"
      "lw %[a6],  8(%[a_remote_group]) \n\t"
      "lw %[a7], 12(%[a_remote_group]) \n\t"
      "lw %[a0],  0(%[a_remote_group]) \n\t"
      "lw %[a1],  4(%[a_remote_group]) \n\t"
      "lw %[a2],  8(%[a_remote_group]) \n\t"
      "lw %[a3], 12(%[a_remote_group]) \n\t"
      "lw %[a4],  0(%[a_remote_group]) \n\t"
      "lw %[a5],  4(%[a_remote_group]) \n\t"
      "lw %[a6],  8(%[a_remote_group]) \n\t"
      "lw %[a7], 12(%[a_remote_group]) \n\t"
      "lw %[a0],  0(%[a_remote_group]) \n\t"
      "lw %[a1],  4(%[a_remote_group]) \n\t"
      "lw %[a2],  8(%[a_remote_group]) \n\t"
      "lw %[a3], 12(%[a_remote_group]) \n\t"
      "lw %[a4],  0(%[a_remote_group]) \n\t"
      "lw %[a5],  4(%[a_remote_group]) \n\t"
      "lw %[a6],  8(%[a_remote_group]) \n\t"
      "lw %[a7], 12(%[a_remote_group]) \n\t"
      "lw %[a0],  0(%[a_remote_group]) \n\t"
      "lw %[a1],  4(%[a_remote_group]) \n\t"
      "lw %[a2],  8(%[a_remote_group]) \n\t"
      "lw %[a3], 12(%[a_remote_group]) \n\t"
      "lw %[a4],  0(%[a_remote_group]) \n\t"
      "lw %[a5],  4(%[a_remote_group]) \n\t"
      "lw %[a6],  8(%[a_remote_group]) \n\t"
      "lw %[a7], 12(%[a_remote_group]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 6b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      : [a0] "=&r"(a0), [a1] "=&r"(a1), [a2] "=&r"(a2),
        [a3] "=&r"(a3), [a4] "=&r"(a4), [a5] "=&r"(a5), [a6] "=&r"(a6),
        [a7] "=&r"(a7), [idx] "+&r"(idx)
      : [im_0] "r"(im_0), [num_loops] "I"(num_loops),
        [a_remote_tile] "r"(addr_remote_tile),
        [a_remote_sub_group] "r"(addr_remote_sub_group),
        [a_remote_group] "r"(addr_remote_group)
      : "memory");
}
