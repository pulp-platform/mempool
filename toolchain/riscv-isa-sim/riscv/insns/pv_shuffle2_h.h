uint8_t src_sel; // select rd or rs1 as source (bit [1] of second operand)
uint8_t half_sel; // select which half from source (bit [0] of second operand)
uint16_t source;
uint32_t simd_rd = 0;

for(int i = xlen/16 - 1; i >= 0; i--){
  half_sel = RS2_H(i) & 0x01; // bit [0] of RS2_H(i)
  src_sel = (RS2_H(i) >> 1) & 0x01; // bit [1] of RS2_H(i)
  source = src_sel ? RS1_H(half_sel) : RD_H(half_sel);
  simd_rd <<= 16;
  simd_rd += (uint32_t)source & 0x0000FFFF;
}

WRITE_RD(sext_xlen(simd_rd));
