sreg_t clip_lower = insn.p_zimm5() ? -(1 << (insn.p_zimm5() - 1)) : -1;
sreg_t clip_upper = insn.p_zimm5() ? ((1 << (insn.p_zimm5() - 1)) - 1) : 0;

if(sreg_t(RS1) <= clip_lower)
  WRITE_RD(clip_lower);
else if(sreg_t(RS1) >= clip_upper)
  WRITE_RD(clip_upper);
else
  WRITE_RD(sreg_t(RS1));
