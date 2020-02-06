.globl _start
.section .text.init;
.section .text;

_start:
    ; Initialize global pointer
    .option push
    .option norelax
    1:auipc gp, %pcrel_hi(__global_pointer$)
      addi  gp, gp, %pcrel_lo(1b)
    .option pop

    /* reset vector */
    j reset_vector
reset_vector:
    li      x1, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0
    li      x7, 0
    li      x8, 0
    li      x9, 0
    li      x10, 0
    li      x11, 0
    li      x12, 0
    li      x13, 0
    li      x14, 0
    li      x15, 0
    li      x16, 0
    li      x17, 0
    li      x18, 0
    li      x19, 0
    li      x20, 0
    li      x10, 0
    li      x21, 0
    li      x22, 0
    li      x23, 0
    li      x24, 0
    li      x25, 0
    li      x26, 0
    li      x27, 0
    li      x28, 0
    li      x29, 0
    li      x30, 0
    li      x31, 0
    la      sp, tcdm_end_address_reg ; load stack top from peripheral register
    lw      sp, 0(sp)
    csrr    a0, mhartid              ; get hart id
    la      a1, nr_cores_address_reg ; get the number of cores per cluster
    lw      a1, 0(a1)
    li      t0, -1                   ; generate a all 1 bitmask
    sll     t0, t0, a1
    neg     t0, t0
    and     t0, a0, t0               ; generate a core id which starts at 0 for each cluster
    slli    t0, t0, 8                ; set some stack-space aside for each hart
    sub     sp, sp, t0
    call    main

eoc:
    la t0, eoc_address
    sw a0, 0(t0)
    jal x0, eoc

fail:
    la t0, eoc_address
    sw a0, 0(t0)
    jal x0, eoc

.section ".eoc_address","aw",@progbits
.align 6
.globl eoc_address
eoc_address: .dword 0

.section .data
