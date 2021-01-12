uint32_t acc = RD;

for(int i = xlen/16 - 1; i >= 0; i--)
  acc += zext16(RS1_H(i)) * insn.p_zimm6();

WRITE_RD(zext_xlen(acc));
