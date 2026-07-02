/* Copyright 2020 ETH Zurich and University of Bologna. */
/* Solderpad Hardware License, Version 0.51, see LICENSE for details. */
/* SPDX-License-Identifier: SHL-0.51 */

/* Merged linker script for flex_cluster with mempool integration. */
/* Includes preprocessed arch.ld for parametric L1/L2/HBM regions. */

INCLUDE arch.ld

OUTPUT_ARCH("riscv")
ENTRY(_start)

PHDRS
{
  l2_phdr  PT_LOAD;
}

SECTIONS
{
  /* L1 sequential region (stacks, per-tile sequential data) - NOLOAD */
  .l1_seq (NOLOAD): {
    . = __seq_end;
  } > l1

  /* L1 interleaved region (shared data, barriers, heap) - NOLOAD */
  .l1 (NOLOAD): {
    *(.l1_prio)
    *(.l1)
    . = ALIGN(4);
    __l1_alloc_base = ALIGN(0x10);
    __l1_heap_start = .;
  } > l1

  /* Program code in L2 (flex_cluster instruction memory at 0x80000000) */
  .text : {
    . = ALIGN(4);
    *(.init)
    *(.text.init)
    *(.text.startup)
    *(.text)
    *(.text*)
    . = ALIGN(4);
    _etext = .;
  } > l2 :l2_phdr

  /* Read-only data in L2 */
  .rodata : {
    . = ALIGN(4);
    *(.rodata)
    *(.rodata*)
    /* Align to 4KiB for RO cache boundary */
    . = ALIGN(0x1000);
    _erodata = .;
  } > l2 :l2_phdr

  /* HTIF section for FESVR */
  .htif : { } > l2 :l2_phdr

  /* Thread Local Storage sections */
  .tdata : {
    __tdata_start = .;
    *(.tdata .tdata.* .gnu.linkonce.td.*)
    __tdata_end = .;
  } > l2 :l2_phdr
  .tbss : {
    __tbss_start = .;
    *(.tbss .tbss.* .gnu.linkonce.tb.*)
    *(.tcommon)
    __tbss_end = .;
  } > l2 :l2_phdr

  /* Cluster Local Storage sections */
  .cdata : {
    __cdata_start = .;
    *(.cdata .cdata.*)
    __cdata_end = .;
  } > l2 :l2_phdr
  .cbss : {
    __cbss_start = .;
    KEEP(*(.cbss .cbss.*))
    __cbss_end = .;
  } > l2 :l2_phdr

  /* used by the startup to initialize data */
  _sidata = LOADADDR(.data);

  /* Small data section addressable through global pointer */
  .sdata : {
    __SDATA_BEGIN__ = .;
    __global_pointer$ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2)
    *(.srodata .srodata.*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  } > l2 :l2_phdr

  /* Initialized data in L2 */
  .data : {
    . = ALIGN(0x10);
    __DATA_BEGIN__ = .;
    *(.data .data.* .gnu.linkonce.d.*)
    SORT(CONSTRUCTORS)
  } > l2 :l2_phdr
  _edata = .; PROVIDE (edata = .);

  /* Small BSS */
  . = .;
  __bss_start = .;
  .sbss : {
    *(.dynsbss)
    *(.sbss .sbss.* .gnu.linkonce.sb.*)
    *(.scommon)
  } > l2 :l2_phdr

  /* Uninitialized data */
  .bss : {
    *(.dynbss)
    *(.bss .bss.* .gnu.linkonce.b.*)
    *(COMMON)
    . = ALIGN(. != 0 ? 32 / 8 : 1);
  } > l2 :l2_phdr
  . = ALIGN(32 / 8);
  . = SEGMENT_START("ldata-segment", .);
  . = ALIGN(32 / 8);
  __BSS_END__ = .;
  __bss_end = .;
  _end = .; PROVIDE (end = .);

  /* Uninitialized data in L2 */
  .dram : {
    *(.dram)
    _edram = .;
  } > l2 :l2_phdr

  /* Additional L2 allocations */
  .l2 : {
    . = ALIGN(0x10);
    *(.l2)
    __l2_alloc_base = ALIGN(0x10);
  } > l2 :l2_phdr

  /* HBM section — NOLOAD. HBM data is injected at run-time via gvsoc's
     --preload <elf> option */
  .hbm (NOLOAD) : {
    *(.hbm_prio)
    . = ALIGN(1024);
    *(.hbm)
    *(.hbm*)
    . = ALIGN(1024);
    __hbm_heap_start = .;
  } > hbm
}
