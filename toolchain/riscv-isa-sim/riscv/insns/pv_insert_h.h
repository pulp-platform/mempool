uint32_t ins_rd = RD;
uint8_t i = insn.p_zimm6() & 0x01; /* select to which rd half to write the 16-bit value */

ins_rd = (ins_rd & ~(0xFFFF << ((xlen >> 1) * i))) | ((RS1_H(0) & 0xFFFF) << ((xlen >> 1) * i));

WRITE_RD(sext_xlen(ins_rd));
