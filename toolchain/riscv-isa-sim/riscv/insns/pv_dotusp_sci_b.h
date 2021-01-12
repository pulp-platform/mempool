int32_t acc = 0;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += sreg_t(zext8(RS1_B(i))) * insn.p_simm6();

WRITE_RD(sext_xlen(acc));
