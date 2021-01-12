int32_t acc = RD;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += sext8(RS1_B(i)) * insn.p_simm6();

WRITE_RD(sext_xlen(acc));
