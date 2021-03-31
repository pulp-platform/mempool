WRITE_RD(MMU.load_uint16(RS1));
WRITE_RS1(RS1 + insn.i_imm());
