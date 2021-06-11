if(sreg_t(RS1) <= 0)
  WRITE_RD(0);
else if(sreg_t(RS1) >= sreg_t(RS2))
  WRITE_RD(sreg_t(RS2));
else
  WRITE_RD(sreg_t(RS1));
