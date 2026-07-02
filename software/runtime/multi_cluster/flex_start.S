# Copyright 2020 ETH Zurich and University of Bologna.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Merged startup for flex_cluster with mempool integration.
# Per-core stack setup, RO cache config, and EOC from mempool crt0.S.
# Mempool config defines (NUM_CORES_PER_TILE, STACK_SIZE, etc.) come
# from -D compiler flags set by CMakeLists.txt.

.include "flex_cluster_arch.inc"

.globl _start
.globl _eoc
.section .text.init;

_start:
    # Initialize global pointer
    .option push
    .option norelax
1:  auipc   gp, %pcrel_hi(__global_pointer$)
    addi    gp, gp, %pcrel_lo(1b)
    .option pop

    j _reset_vector

_reset_vector:
    # Clear all general-purpose registers
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

    # === Per-core stack setup (from mempool crt0.S) ===
    la      sp, __stack_start                                   # load stack base
    csrr    a0, mhartid                                         # get hart id

    # Calculate sequential region offset for our tile
    # tile_id = hartid / NUM_CORES_PER_TILE
    srli    t0, a0, LOG2_NUM_CORES_PER_TILE
    # tile_offset = tile_id * NUM_CORES_PER_TILE * SEQ_MEM_SIZE
    slli    t0, t0, (LOG2_NUM_CORES_PER_TILE + LOG2_SEQ_MEM_SIZE)

    # Calculate stack offset within tile
    # tile_core_id = hartid % NUM_CORES_PER_TILE
    li      t1, NUM_CORES_PER_TILE
    addi    t1, t1, -1                                          # create mask
    and     t1, a0, t1                                          # tile_core_id
    addi    t1, t1, 1                                           # tile_core_id + 1
    # tile_core_offset = (tile_core_id + 1) * STACK_SIZE - 4
    slli    t1, t1, LOG2_STACK_SIZE
    addi    t1, t1, -4

    # Calculate final stack pointer
    add     t0, t0, t1                                          # offset = tile_offset + tile_core_offset
    add     sp, sp, t0                                          # sp = __stack_start + offset

    # Add offset for hardware queues at beginning of sequential memory
    li      t0, XQUEUE_SIZE                                     # XQUEUE_SIZE (in words)
    slli    t0, t0, (4+2)                                       # * BANKS_PER_TILE * BYTES_PER_WORD
    add     sp, sp, t0

    # Write the stack limit into the dedicated CSR
    addi    t0, sp, -(STACK_SIZE-4)                             # stack_limit
    csrw    0x7D0, t0                                           # stacklimit CSR

    # Configure RO cache (core 0 only)
    bnez    a0, _jump_main
    li      t0, (0x40000000 + 0x58)                             # CTRL_REG + RO_CACHE_END_0
    la      t1, _erodata                                        # end of read-only data
    sw      t1, 0(t0)

_jump_main:
    call    main

_eoc:
    # EOC: write (hartid<<1)|1 to mempool control register
    li      t0, 0x40000000                                      # CTRL_REG + EOC (offset 0x0)
    csrr    a0, mhartid
    slli    t1, a0, 1
    addi    t1, t1, 1
    sw      t1, 0(t0)

    # Return to ROM so the cluster safely parks in boot code waiting for next work.
    la      ra, __rom_start
    ret

.section .data
