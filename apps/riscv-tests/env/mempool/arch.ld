SECTIONS {
  ROM_BASE = 0x80000000;
  . = 0x0;
  .l1_seq : { *(.l1_seq) }
  l1__seq_alloc_base = ALIGN(0x10);
  . = (16 * 0x400);
  /* placing *(.bss) in .l1 is an hack to make test cases for atomics work not fail due to race conditions */
  .l1 : { *(.l1) *(.bss) }
  l1_alloc_base = ALIGN(0x10);
  tcdm_start_address_reg = 0x40000000;
  tcdm_end_address_reg = 0x40000004;
  nr_cores_address_reg = 0x40000008;
  fake_uart = 0xC0000000;
  . = 0xD0000000;
  .eoc_address (NOLOAD): {
    *(.eoc_address)
  }
}
