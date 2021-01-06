int16_t temp;
uint32_t simd_rd = 0;

for(int i = xlen/16 - 1; i >= 0; i--){
  temp = sext16(RS1_H(i)) > 0 ? RS1_H(i) : -sext16(RS1_H(i));
  simd_rd <<= 16;
  simd_rd += (uint32_t)temp & 0x0000FFFF;
}
WRITE_RD(sext_xlen(simd_rd));
