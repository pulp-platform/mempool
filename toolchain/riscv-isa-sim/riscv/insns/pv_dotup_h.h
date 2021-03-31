uint32_t acc = 0;

for(int i = xlen/16 - 1; i >= 0; i--)
  acc += zext16(RS1_H(i)) * zext16(RS2_H(i));

WRITE_RD(sext_xlen(acc));
