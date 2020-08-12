OUTPUT_ARCH("riscv")
ENTRY(_start)

/* Include the file processed by the preprocessor called common/arch.ld.c */
INCLUDE common/arch.ld

SECTIONS {
  . = 0x80010000;
  .text : {
    *(.text.init)
    *(.text)
  }

  . = ALIGN(0x10);
  .data           : { *(.data) }
  .rodata         : { *(.rodata .rodata.* .gnu.linkonce.r.*) }
  .rodata1        : { *(.rodata1) }
  .sdata2         : {
    *(.sdata2 .sdata2.* .gnu.linkonce.s2.*)
  }
  .sdata          : {
    __global_pointer$ = . + 0x800;
    *(.srodata.cst16) *(.srodata.cst8) *(.srodata.cst4) *(.srodata.cst2) *(.srodata .srodata.*)
    *(.sdata .sdata.* .gnu.linkonce.s.*)
  }
  . = .;

  __bss_start = .;
  .sbss2          : { *(.sbss2 .sbss2.* .gnu.linkonce.sb2.*) }
  .bss            : { *(.bss) }
  __bss_end = .;

  . = ALIGN(0x10);
  .l2             : { *(.l2) }
  l2_alloc_base = ALIGN(0x10);
}
