/* Copyright 2020 ETH Zurich and University of Bologna. */
/* Solderpad Hardware License, Version 0.51, see LICENSE for details. */
/* SPDX-License-Identifier: SHL-0.51 */

/* DEV-ONLY: SoftHier-Deeploy Integration */

OUTPUT_ARCH( "riscv" )
ENTRY(_start)

PHDRS
{
  l3   PT_LOAD;
}

/* Memory section should be provided in a separate, platform-specific */
/* file. It should define at least the L1 and L3 memory blocks. */
MEMORY
{
    L1  (rwxa) : ORIGIN = 0x00000010, LENGTH = 0x00100000
    L3  (rwxa) : ORIGIN = 0x80000000, LENGTH = 0x80000000
    HBM (rwxa) : ORIGIN = 0xc0000000, LENGTH = 0x20000000
}

SECTIONS
{
  .l1 (NOLOAD) :
  {
    __l1_data_start = .;
    *(.l1_prio)
    *(.l1)
    . = ALIGN(4);
    __l1_heap_start = .;
    __l1_end = .;
  } >L1 

  /* Program code goes into L3 */
  .text :
  {
    . = ALIGN(4);
    *(.init)
    *(.text.init)
    *(.text.startup)
    *(.text)
    *(.text*)
    *(.text)
    . = ALIGN(4);
    _etext = .;
  } >L3 :l3

  /* By default, constant data goes into L3, right after code section */
  .rodata :
  {
    . = ALIGN(4);
    *(.rodata)
    *(.rodata*)
    . = ALIGN(4);
  } >L3 :l3

  /* HTIF section for FESVR */
  .htif         : { } >L3 :l3

  /* Thread Local Storage sections */
  .tdata    :
  {
    __tdata_start = .;
    *(.tdata .tdata.* .gnu.linkonce.td.*)
    __tdata_end = .;
  } >L3 :l3
  .tbss :
  {
    __tbss_start = .;
    *(.tbss .tbss.* .gnu.linkonce.tb.*)
    *(.tcommon)
    __tbss_end = .;
    __tbss_end2 = .;
  } >L3 :l3
  /* add a section after .tbss to put the __tbss_end symbol into for
     the LLD linker */
  /* .tbssend : { __tbss_end2 = .; } */

  /* Cluster Local Storage sections */
  .cdata    :
  {
    __cdata_start = .;
    *(.cdata .cdata.*)
    __cdata_end = .;
  } >L3 :l3
  .cbss :
  {
    __cbss_start = .;
    KEEP(*(.cbss .cbss.*))
    __cbss_end = .;
  } >L3 :l3

  /* used by the startup to initialize data */
  _sidata = LOADADDR(.data);

  /* small data section that can be addressed through the global pointer */
  .sdata          :
  {
    __SDATA_BEGIN__ = .;
    __global_pointer$ = . + 0x7f0;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata .srodata.*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  } >L3 :l3

  /* Initialized data sections goes into L3 */
  .data :
  {
    __DATA_BEGIN__ = .;
    *(.data .data.* .gnu.linkonce.d.*)
    SORT(CONSTRUCTORS)
  } >HBM :hbm
  _edata = .; PROVIDE (edata = .);

  /* small bss section */
  . = .;
  __bss_start = .;
  .sbss           :
  {
    *(.dynsbss)
    *(.sbss .sbss.* .gnu.linkonce.sb.*)
    *(.scommon)
  } >L3 :l3

  /* Uninitialized data section */
  .bss            :
  {
   *(.dynbss)
   *(.bss .bss.* .gnu.linkonce.b.*)
   *(COMMON)
   /* Align here to ensure that the .bss section occupies space up to
      _end.  Align after .bss to ensure correct alignment even if the
      .bss section disappears because there are no input sections. */
   . = ALIGN(. != 0 ? 32 / 8 : 1);
  } >L3 :l3
  . = ALIGN(32 / 8);
  . = SEGMENT_START("ldata-segment", .);
  . = ALIGN(32 / 8);
  __BSS_END__ = .;
  __bss_end = .;
  _end = .; PROVIDE (end = .);


  /* Uninitialized data section in L3 */
  .dram :
  {
    *(.dram)
    _edram = .;
  } >L3 :l3

  /* HBM section — NOLOAD. HBM data is injected at run-time via gvsoc's
     --preload <elf> option; */
  .hbm (NOLOAD) :
  {
    *(.hbm_prio)
    . = ALIGN(1024);
    *(.hbm)
    *(.hbm*)
    . = ALIGN(1024);
    __hbm_heap_start = .;
  } >HBM

}