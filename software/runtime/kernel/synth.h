// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include "runtime.h"

static inline void power_profile(int32_t *const a) {
  // Who am I?
  uint32_t core_id = mempool_get_core_id();
  // Calculate unique address in remote bank
  uint32_t tile_id = (core_id / NUM_CORES_PER_TILE) % NUM_TILES_PER_GROUP;
  uint32_t remote_group = core_id % NUM_CORES_PER_TILE;
  uint32_t remote_tile =
      (NUM_TILES_PER_GROUP * remote_group) +
      ((tile_id + (NUM_TILES_PER_GROUP / 2)) % NUM_TILES_PER_GROUP);
  uint32_t remote_bank = (remote_tile * NUM_BANKS_PER_TILE) +
                         ((core_id / NUM_CORES_PER_GROUP) *
                          (NUM_BANKS_PER_TILE / NUM_CORES_PER_TILE));
  // Address to load from are [addr:addr+3]
  volatile int32_t *addr_remote = &a[remote_bank];
  volatile int32_t *addr_local =
      &a[core_id * (NUM_BANKS_PER_TILE / NUM_CORES_PER_TILE)];
  // Do this loop M times
  int const num_loops = 2;
  int32_t op_a0 = 1763350245;
  int32_t op_a1 = -473677120;
  int32_t op_a2 = -1893217350;
  int32_t op_a3 = -915173234;
  int32_t op_a4 = -715022251;
  int32_t op_a5 = 1755108161;
  int32_t op_a6 = 1629317995;
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
      // Outer loop: Calculate four elements of C. Execute this loop P times
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
      "lw %[a0],  0(%[a_remote]) \n\t"
      "lw %[a1],  4(%[a_remote]) \n\t"
      "lw %[a2],  8(%[a_remote]) \n\t"
      "lw %[a3], 12(%[a_remote]) \n\t"
      "lw %[a4],  0(%[a_remote]) \n\t"
      "lw %[a5],  4(%[a_remote]) \n\t"
      "lw %[a6],  8(%[a_remote]) \n\t"
      "lw %[a7], 12(%[a_remote]) \n\t"
      "lw %[a0],  0(%[a_remote]) \n\t"
      "lw %[a1],  4(%[a_remote]) \n\t"
      "lw %[a2],  8(%[a_remote]) \n\t"
      "lw %[a3], 12(%[a_remote]) \n\t"
      "lw %[a4],  0(%[a_remote]) \n\t"
      "lw %[a5],  4(%[a_remote]) \n\t"
      "lw %[a6],  8(%[a_remote]) \n\t"
      "lw %[a7], 12(%[a_remote]) \n\t"
      "lw %[a0],  0(%[a_remote]) \n\t"
      "lw %[a1],  4(%[a_remote]) \n\t"
      "lw %[a2],  8(%[a_remote]) \n\t"
      "lw %[a3], 12(%[a_remote]) \n\t"
      "lw %[a4],  0(%[a_remote]) \n\t"
      "lw %[a5],  4(%[a_remote]) \n\t"
      "lw %[a6],  8(%[a_remote]) \n\t"
      "lw %[a7], 12(%[a_remote]) \n\t"
      "lw %[a0],  0(%[a_remote]) \n\t"
      "lw %[a1],  4(%[a_remote]) \n\t"
      "lw %[a2],  8(%[a_remote]) \n\t"
      "lw %[a3], 12(%[a_remote]) \n\t"
      "lw %[a4],  0(%[a_remote]) \n\t"
      "lw %[a5],  4(%[a_remote]) \n\t"
      "lw %[a6],  8(%[a_remote]) \n\t"
      "lw %[a7], 12(%[a_remote]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 2b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "3: \n\t"
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
      "bne %[idx], %[im_0], 3b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "4: \n\t"
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
      "bne %[idx], %[im_0], 4b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "5: \n\t"
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
      "bne %[idx], %[im_0], 5b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      : [op_0] "=&r"(op_0), [op_1] "=&r"(op_1), [op_2] "=&r"(op_2),
        [op_3] "=&r"(op_3), [a0] "=&r"(a0), [a1] "=&r"(a1), [a2] "=&r"(a2),
        [a3] "=&r"(a3), [a4] "=&r"(a4), [a5] "=&r"(a5), [a6] "=&r"(a6),
        [a7] "=&r"(a7), [idx] "+&r"(idx)
      : [im_0] "r"(im_0), [num_loops] "I"(num_loops), [op_a0] "r"(op_a0),
        [op_a1] "r"(op_a1), [op_a2] "r"(op_a2), [op_a3] "r"(op_a3),
        [op_a4] "r"(op_a4), [op_a5] "r"(op_a5), [op_a6] "r"(op_a6),
        [op_a7] "r"(op_a7), [a_local] "r"(addr_local),
        [a_remote] "r"(addr_remote)
      : "memory");
}
