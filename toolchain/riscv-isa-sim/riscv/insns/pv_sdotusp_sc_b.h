int32_t acc = RD;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += sreg_t(zext8(RS1_B(i))) * sext8(RS2_B(0));

WRITE_RD(sext_xlen(acc));
