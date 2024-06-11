/* Copyright 2021 ETH Zurich and University of Bologna. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

/* Include the file processed by the preprocessor called arch.ld.c */
INCLUDE arch.ld

OUTPUT_ARCH("riscv")
ENTRY(_start)


SECTIONS {
  /* Sequential region on L1 */
  /* Use dynamic allocation with `domain_malloc` */
  .l1_seq (NOLOAD): {
    . = __seq_end;
  } > l1

  /* Interleaved region on L1 */
  .l1 (NOLOAD): {
    *(.l1_prio)
    *(.l1)
    __l1_alloc_base = ALIGN(0x10);
    __heap_start = .;
  } > l1

  .bss : {
    __bss_start = .;
    *(.bss)
    *(.sbss .sbss2 .sbss2.* .gnu.linkonce.sb2.*);
    __bss_end = .;
  } > l1

  /* Instructions on L2 */
  .text : {
    *(.text.init)
    *(.text.startup)
    *(.text)
    *(.text.end)
    . = ALIGN(0x40);
    _etext = .;
  } > l2

  /* Init array on L2 */
  .init_array : {
      HIDDEN (__init_array_start = .);
      KEEP (*(SORT_BY_INIT_PRIORITY(.init_array.*)))
      KEEP (*(.init_array))
      HIDDEN (__init_array_end = .);
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
    . = ALIGN(0x10);
  } > l2

  .l2 : {
    . = ALIGN(0x10);
    *(.l2)
    __l2_alloc_base = ALIGN(0x10);
  } > l2

  .comment : {
    *(.comment)
  }
}
