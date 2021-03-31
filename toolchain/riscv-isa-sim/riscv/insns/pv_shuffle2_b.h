uint8_t src_sel; // select rd or rs1 as source (bit [2] of second operand)
uint8_t byte_sel; // select which byte from source (bits [1:0] of second operand)
uint8_t source;
uint32_t simd_rd = 0;

for(int i = xlen/8 - 1; i >= 0; i--){
  byte_sel = RS2_B(i) & 0x03; // bits [1:0] of RS2_B(i)
  src_sel = (RS2_B(i) >> 2) & 0x01; // bit [2] of RS2_B(i)
  source = src_sel ? RS1_B(byte_sel) : RD_B(byte_sel);
  simd_rd <<= 8;
  simd_rd += (uint32_t)source & 0x000000FF;
}

WRITE_RD(sext_xlen(simd_rd));
