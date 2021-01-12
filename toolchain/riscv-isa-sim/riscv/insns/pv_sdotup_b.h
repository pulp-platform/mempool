uint32_t acc = RD;

for(int i = xlen/8 - 1; i >= 0; i--)
  acc += zext8(RS1_B(i)) * zext8(RS2_B(i));

WRITE_RD(zext_xlen(acc));
