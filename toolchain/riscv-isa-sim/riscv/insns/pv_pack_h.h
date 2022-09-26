uint32_t ins_rd = RD;

ins_rd = ((RS1_H(0) & 0xFFFF) << (xlen >> 1)) | ((uint32_t)(RS1_H(0)) & 0x0000FFFF);

WRITE_RD(sext_xlen(ins_rd));
