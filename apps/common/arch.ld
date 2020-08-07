SECTIONS {
    ROM_BASE = 0x80000000; /* ... but actually position independent */

    . = 0x0;
    .l1_seq : { *(.l1_seq) }
    l1__seq_alloc_base = ALIGN(0x10);

    /*. = 0x08000; /*  32x1KiB */
    . = 0x10000; /*  64x1KiB */
    /*. = 0x20000; /* 128x1KiB */
    /*. = 0x30000; /* 256x1KiB */
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
