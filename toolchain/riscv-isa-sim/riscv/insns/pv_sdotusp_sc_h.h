int32_t acc = RD;

for(int i = xlen/16 - 1; i >= 0; i--)
  acc += sreg_t(zext16(RS1_H(i))) * sext16(RS2_H(0));

WRITE_RD(sext_xlen(acc));
