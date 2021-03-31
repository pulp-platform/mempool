int32_t acc = 0;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += sext8(RS1_B(i)) * sext8(RS2_B(i));

WRITE_RD(sext_xlen(acc));
