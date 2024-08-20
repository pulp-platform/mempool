// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This file will get processed by the precompiler to expand all macros. */

MEMORY {
  l1 (R) : ORIGIN = 0x00000000, LENGTH = (NUM_CORES * BANKING_FACTOR * L1_BANK_SIZE)
  l2     : ORIGIN = L2_BASE   , LENGTH = L2_SIZE
  rom (R): ORIGIN = BOOT_ADDR , LENGTH = 0x00001000
}

SECTIONS {
  // Start end end of memories
  __l1_start = ORIGIN(l1);
  __l1_end = ORIGIN(l1) + LENGTH(l1);
  __l2_start = ORIGIN(l2);
  __l2_end = ORIGIN(l2) + LENGTH(l2);
  __rom_start = ORIGIN(rom);
  __rom_end = ORIGIN(rom) + LENGTH(rom);

  // Stack size
  __stack_start = __l1_start;
  __stack_end = __l1_start + (NUM_CORES * STACK_SIZE);

  // Sequential region size
  __seq_start = __l1_start;
  __seq_end = __l1_start + (NUM_CORES * SEQ_MEM_SIZE);

  // Heap size (start address is re-assigned in link.ld)
  __heap_start = __l1_start;
  __heap_end = __l1_end;

  fake_uart              = 0xC0000000;
}
