uint32_t acc = 0;

for(int i = xlen/16 - 1; i >= 0; i--)
  acc += zext16(RS1_H(i)) * insn.p_zimm6();

WRITE_RD(sext_xlen(acc));
