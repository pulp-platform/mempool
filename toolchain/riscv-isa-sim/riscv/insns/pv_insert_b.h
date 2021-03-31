uint32_t ins_rd = RD;
uint8_t i = insn.p_zimm6() & 0x03; /* select to which rd half to write the 16-bit value */

ins_rd = (ins_rd & ~(0xFF << ((xlen >> 2) * i))) | ((RS1_H(0) & 0xFF) << ((xlen >> 2) * i));

WRITE_RD(sext_xlen(ins_rd));
