// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Xpulp post-incrementing loads and stores for inline assembly.
//
// GCC and LLVM use a different syntax for these instructions. Code shared by
// both compilers builds the instruction strings with the macros below, e.g.
//   P_LW_IRPOST("x12", "%[addr_b]", "4")    // x12 = *addr_b; addr_b += 4
//   P_SW_RRPOST("x16", "%[addr_c]", "%[s]") // *addr_c = x16; addr_c += s
// IRPOST takes an immediate increment, RRPOST a register increment.

#ifndef __XPULP_POSTMOD_H__
#define __XPULP_POSTMOD_H__

#ifdef __clang__
#define P_LW_IRPOST(rd, rs1, imm) "p.lw.irpost " rd ", (" rs1 "), " imm " \n\t"
#define P_LW_RRPOST(rd, rs1, rs2) "p.lw.rrpost " rd ", (" rs1 "), " rs2 " \n\t"
#define P_SW_IRPOST(rs2, rs1, imm)                                             \
  "p.sw.irpost " rs2 ", (" rs1 "), " imm " \n\t"
#define P_SW_RRPOST(rs2, rs1, rs3)                                             \
  "p.sw.rrpost " rs2 ", (" rs1 "), " rs3 " \n\t"
#else
#define P_LW_IRPOST(rd, rs1, imm) "p.lw " rd ", " imm "(" rs1 "!) \n\t"
#define P_LW_RRPOST(rd, rs1, rs2) "p.lw " rd ", " rs2 "(" rs1 "!) \n\t"
#define P_SW_IRPOST(rs2, rs1, imm) "p.sw " rs2 ", " imm "(" rs1 "!) \n\t"
#define P_SW_RRPOST(rs2, rs1, rs3) "p.sw " rs2 ", " rs3 "(" rs1 "!) \n\t"
#endif

#endif // __XPULP_POSTMOD_H__
