int8_t temp;
uint32_t simd_rd = 0;

for(int i = xlen/8 - 1; i >= 0; i--){
  temp = sext8(RS1_B(i)) >> (zext8(RS2_B(0)) & 0x07);
  simd_rd <<= 8;
  simd_rd += (uint32_t)temp & 0x000000FF;
}
WRITE_RD(sext_xlen(simd_rd));
