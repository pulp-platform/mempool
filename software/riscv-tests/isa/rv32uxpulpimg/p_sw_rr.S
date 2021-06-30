# See LICENSE for license details.

#*****************************************************************************
# p_sw_rr.S
#-----------------------------------------------------------------------------
#
# Test p.sw (register-register) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_ST_RR_OP( 2, p.sw, lw, 0x00aa00aa,  0, tdat );
  TEST_ST_RR_OP( 3, p.sw, lw, 0xaa00aa00,  4, tdat );
  TEST_ST_RR_OP( 4, p.sw, lw, 0x0aa00aa0,  8, tdat );
  TEST_ST_RR_OP( 5, p.sw, lw, 0xa00aa00a, 12, tdat );

  # Negative offset
  TEST_ST_RR_OP( 6, p.sw, lw, 0x00aa00aa, -12, tdat8 );
  TEST_ST_RR_OP( 7, p.sw, lw, 0xaa00aa00,  -8, tdat8 );
  TEST_ST_RR_OP( 8, p.sw, lw, 0x0aa00aa0,  -4, tdat8 );
  TEST_ST_RR_OP( 9, p.sw, lw, 0xa00aa00a,   0, tdat8 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_ST_RR_SRC12_BYPASS( 10, 0, 0, p.sw, lw, 0xaabbccdd,  0, tdat );
  TEST_ST_RR_SRC12_BYPASS( 11, 0, 1, p.sw, lw, 0xdaabbccd,  4, tdat );
  TEST_ST_RR_SRC12_BYPASS( 12, 0, 2, p.sw, lw, 0xddaabbcc,  8, tdat );
  TEST_ST_RR_SRC12_BYPASS( 13, 1, 0, p.sw, lw, 0xcddaabbc, 12, tdat );
  TEST_ST_RR_SRC12_BYPASS( 14, 1, 1, p.sw, lw, 0xccddaabb, 16, tdat );
  TEST_ST_RR_SRC12_BYPASS( 15, 2, 0, p.sw, lw, 0xbccddaab, 20, tdat );

  TEST_ST_RR_SRC21_BYPASS( 16, 0, 0, p.sw, lw, 0x00112233,  0, tdat );
  TEST_ST_RR_SRC21_BYPASS( 17, 0, 1, p.sw, lw, 0x30011223,  4, tdat );
  TEST_ST_RR_SRC21_BYPASS( 18, 0, 2, p.sw, lw, 0x33001122,  8, tdat );
  TEST_ST_RR_SRC21_BYPASS( 19, 1, 0, p.sw, lw, 0x23300112, 12, tdat );
  TEST_ST_RR_SRC21_BYPASS( 20, 1, 1, p.sw, lw, 0x22330011, 16, tdat );
  TEST_ST_RR_SRC21_BYPASS( 21, 2, 0, p.sw, lw, 0x12233001, 20, tdat );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat0:  .word 0xdeadbeef
tdat1:  .word 0xdeadbeef
tdat2:  .word 0xdeadbeef
tdat3:  .word 0xdeadbeef
tdat4:  .word 0xdeadbeef
tdat5:  .word 0xdeadbeef
tdat6:  .word 0xdeadbeef
tdat7:  .word 0xdeadbeef
tdat8:  .word 0xdeadbeef
tdat9:  .word 0xdeadbeef

RVTEST_DATA_END

