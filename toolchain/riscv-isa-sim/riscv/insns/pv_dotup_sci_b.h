uint32_t acc = 0;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += zext8(RS1_B(i)) * insn.p_zimm6();

WRITE_RD(zext_xlen(acc));
