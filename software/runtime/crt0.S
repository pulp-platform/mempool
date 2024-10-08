// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
//         Matheus Cavalcante, ETH Zurich

// #define TOP4_STACK

#include "addrmap.h"

.globl _start
.globl _eoc
.section .text;
.section .text.init;

_start:
    // Initialize global pointer
    .option push
    .option norelax
    1:auipc gp, %pcrel_hi(__global_pointer$)
      addi  gp, gp, %pcrel_lo(1b)
    .option pop

    /* reset vector */
    j _reset_vector
_reset_vector:
    li      x1, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0
    li      x7, 0
    li      x8, 0
    li      x9, 0
    li      x10, 0
    li      x11, 0
    li      x12, 0
    li      x13, 0
    li      x14, 0
    li      x15, 0
    li      x16, 0
    li      x17, 0
    li      x18, 0
    li      x19, 0
    li      x20, 0
    li      x10, 0
    li      x21, 0
    li      x22, 0
    li      x23, 0
    li      x24, 0
    li      x25, 0
    li      x26, 0
    li      x27, 0
    li      x28, 0
    li      x29, 0
    li      x30, 0
    li      x31, 0
    la      sp, __stack_start                                   // load stack
    csrr    a0, mhartid                                         // get hart id
    // Calculate sequential region offset for our tile
    srli    t0, a0, LOG2_NUM_CORES_PER_TILE                     // tile_id = id / NUM_CORES_PER_TILE
    slli    t0, t0, (LOG2_NUM_CORES_PER_TILE+LOG2_SEQ_MEM_SIZE) // tile_offset = tile_id * NUM_CORES_PER_TILE * SEQ_MEM_SIZE
    // Calculate stack offset within tile
    li      t1, NUM_CORES_PER_TILE                              // NUM_CORES_PER_TILE
    addi    t1, t1, -1                                          // Create mask for NUM_CORES_PER_TILE
    and     t1, a0, t1                                          // tile_core_id = id % 4
    addi    t1, t1, 1                                           // tile_core_id += 1
    slli    t1, t1, LOG2_STACK_SIZE                             // tile_core_offset = tile_core_id * STACK_SIZE
    addi    t1, t1, -4                                          // tile_core_offset -= 1 word
    // Calculate final stack pointer
    add     t0, t0, t1                                          // offset = tile_offset + tile_core_offset
    add     sp, sp, t0                                          // sp += offset
    // Add offset in case we have hardware queues at the beginning of sequential memory
    li      t0, XQUEUE_SIZE                                     // XQUEUE_SIZE (in words)
    slli    t0, t0, (4+2)                                       // XQUEUE_SIZE * BANKS_PER_TILE * BYTES_PER_WORD
    add     sp, sp, t0                                          // offset += 16 * xqueue_size * 4
    // Write the stack limit into the dedicated CSR
    addi    t0, sp, -(STACK_SIZE-4)                             // stack_limit = sp - (STACK_SIZE - 1)
    csrw    stacklimit, t0                                     // write stack limit into CSR
    // Configure the RO cache or directly jump to main
    bnez    a0, _jump_main
    li      t0, (CONTROL_REGISTER_OFFSET + CONTROL_REGISTERS_RO_CACHE_END_0_REG_OFFSET) // Get peripheral register to set cacheable region
    la      t1, _erodata                                        // Write the end of the read-only data to be cacheable
    sw      t1, 0(t0)
_jump_main:
    call    main

_eoc:
    li      t0, (CONTROL_REGISTER_OFFSET + CONTROL_REGISTERS_EOC_REG_OFFSET)
    slli    t1, a0, 1
    addi    t1, t1, 1
    sw      t1, 0(t0)
    la      ra, __rom_start
    ret

.section .data
