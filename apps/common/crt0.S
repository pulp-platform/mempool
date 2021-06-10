// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
//         Matheus Cavalcante, ETH Zurich

// #define TOP4_STACK

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
    la      sp, tcdm_start_address_reg // load stack top from peripheral register
    lw      sp, 0(sp)
    csrr    a0, mhartid                // get hart id
#ifdef TOP4_STACK
    srli    t0, a0, 4                  // id / 16
    li      t1, 12288                  // 12 * 2^10
    mul     t1, t0, t1                 // * 12 * 2^10
    andi    t0, a0, 3                  // id % 4
    slli    t0, t0, 12                 // * 2^12
    add     sp, sp, t0                 // sp += (id % 4) * 2^12
    add     sp, sp, t1                 // sp += (id / 16) * 12 * 2^10
    srli    t0, a0, 2                  // id / 4
    slli    t0, t0, 10                 // * 2^10
    add     sp, sp, t0                 // sp += (id / 4 + 1) * 2^10
    addi    sp, sp, 1020               // sp += 2^10-1 (start at stack of next core)
#else
    addi    t0, a0, 1
    slli    t0, t0, 10                 // set some stack-space aside for each hart
    addi    t0, t0, -4                 // Subtract one word to avoid overlapping
    add     sp, sp, t0
#endif
    call    main

_eoc:
    la      t0, eoc_reg
    slli    t1, a0, 1
    addi    t1, t1, 1
    sw      t1, 0(t0)
    la      ra, __rom_start
    ret

.section .data
