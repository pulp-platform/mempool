/* This file will get processed by the precompiler to expand all macros. */

SECTIONS {
  ROM_BASE = 0x80000000; /* ... but actually position independent */

  . = 0x0;
  .l1_seq : { *(.l1_seq) }
  l1__seq_alloc_base = ALIGN(0x10);

  . = (NUM_CORES * 0x400); /* NUM_CORES * 1KiB */
  .l1_prio : { *(.l1_prio) }
  .l1 : { *(.l1) }
  l1_alloc_base = ALIGN(0x10);

  tcdm_start_address_reg = 0x40000000;
  tcdm_end_address_reg   = 0x40000004;
  nr_cores_address_reg   = 0x40000008;

  fake_uart = 0xC0000000;

  . = 0xD0000000;
  .eoc_address (NOLOAD): {
    *(.eoc_address)
  }
}
