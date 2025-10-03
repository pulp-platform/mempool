// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Danilo Cammarata <dcammarata@iis.ee.ethz.ch>
//

  .section .text
  .global _start
_start:

  # Cluster PEs will also starts here to avoid aligning another entry point
  # Just re-route them to the right entry
  csrr    a0, mhartid
  andi    a1, a0, 0x1f
  srli    a0, a0, 5
  # Enabling CV32E40P mstatus.MIE
  li      t0, 0x1
  csrrs   zero, mstatus, t0
  # Enabling CV32E40P SW interrupt (mie[3])
  li      t0, 0x8
  csrrs   zero, mie, t0

  # clear the bss segment
  la      t0, _bss_start
  la      t1, _bss_end
1:
  sw      zero, 0(t0)
  addi    t0, t0, 4
  bltu    t0, t1, 1b

  /* Stack initialization */
  la   x2, stack

.section .text

  // On all other chips we simply pass 0.
  addi  a0, x0, 0
  addi  a1, x0, 0

  // Jump to main program entry point (argc = a0, argv = a1).
  la    t2, main
  jalr  x1, t2
  mv    s0, a0

  /* If program returns from main, call exit routine */
  mv   a0, s0
  wfi

  .global _init
  .global _fini
_init:
_fini:
  # These don't have to do anything since we use init_array/fini_array.
  ret

.section .vectors, "ax"
.option norvc;

  .org 0x80
  jal x0, _start

