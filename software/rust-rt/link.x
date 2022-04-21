/* Copyright 2021 ETH Zurich and University of Bologna. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Include the file processed by the preprocessor called arch.ld.c */

MEMORY {
  l1 (R) : ORIGIN = 0x00000000, LENGTH = 0x1000 /* NUM_CORES * 4 * 1KiB per bank */
  l2     : ORIGIN = 0x80000000, LENGTH = 0x10000
  rom (R): ORIGIN = 0xA0000000, LENGTH = 0x00001000
}

SECTIONS {
  /* Start end end of memories */
  __l1_start = ORIGIN(l1);
  __l1_end = ORIGIN(l1) + LENGTH(l1);
  __l2_start = ORIGIN(l2);
  __l2_end = ORIGIN(l2) + LENGTH(l2);
  __rom_start = ORIGIN(rom);
  __rom_end = ORIGIN(rom) + LENGTH(rom);

  /* Stack size */
  __stack_start = __l1_start;
  __stack_end = __l1_start + 0x400;

  /* Hardware register location */
  eoc_reg                = 0x40000000;
  wake_up_reg            = 0x40000004;
  tcdm_start_address_reg = 0x40000008;
  tcdm_end_address_reg   = 0x4000000C;
  nr_cores_address_reg   = 0x40000010;
  ro_cache_enable        = 0x40000014;
  ro_cache_flush         = 0x40000018;
  ro_cache_start_0       = 0x4000001C;
  ro_cache_end_0         = 0x40000020;
  ro_cache_start_1       = 0x40000024;
  ro_cache_end_1         = 0x40000028;
  ro_cache_start_2       = 0x4000002C;
  ro_cache_end_2         = 0x40000030;
  ro_cache_start_3       = 0x40000034;
  ro_cache_end_3         = 0x40000038;

  fake_uart              = 0xC0000000;
}

OUTPUT_ARCH("riscv")
ENTRY(_start)


SECTIONS {
  /* Sequential region on L1 */
  .l1_seq (NOLOAD): {
    . = __stack_end;
    *(.l1_seq);
    __l1_seq_alloc_base = ALIGN(0x10);
  } > l1

  /* Interleaved region on L1 */
  .l1 (NOLOAD): {
    *(.l1_prio)
    *(.l1)
    *(.bss)
    __l1_alloc_base = ALIGN(0x10);
  } > l1

  /* Instructions on L2 */
  .text : {
    *(.text.init)
    *(.text.startup)
    *(.text.main)
    *(.text)
    *(.text.end)
    /*. = ALIGN(0x40);*/
    _etext = .;
  } > l2

  /* RO Data on L2 */
  .rodata : {
    *(.rodata .rodata.* .gnu.linkonce.r.*)
  } > l2
  .rodata1 : {
    *(.rodata1)
    /* Align non-cacheable regions to 4KiB boundary */
    . = ALIGN(0x1000);
    _erodata = .;
  } > l2

  /* Data on L2 */
  .data           : {
    . = ALIGN(0x10);
    *(.data)
  } > l2
  .sdata2 : {
    *(.sdata2 .sdata2.* .gnu.linkonce.s2.*)
  } > l2
  .sdata : {
    __global_pointer$ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata .srodata.*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  } > l2

  .bss : {
    __bss_start = .;
    *(.bss)
    *(.sbss2 .sbss2.* .gnu.linkonce.sb2.*);
    __bss_end = .;
  } > l2

  .l2 : {
    . = ALIGN(0x10);
    *(.l2)
    __l2_alloc_base = ALIGN(0x10);
  } > l2

  .comment : {
    *(.comment)
  } > l2
}
