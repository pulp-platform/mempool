uint32_t ins_rd = RD;

ins_rd = ((RS1_H(1) << (xlen >> 1)) & 0xFFFF0000) | (RS2_H(1) & 0x0000FFFF);

WRITE_RD(sext_xlen(ins_rd));
