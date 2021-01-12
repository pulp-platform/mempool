uint32_t acc = RD;

for(int i = xlen/16 - 1; i >= 0; i--)
  acc += zext16(RS1_H(i)) * zext16(RS2_H(i));

WRITE_RD(zext_xlen(acc));
