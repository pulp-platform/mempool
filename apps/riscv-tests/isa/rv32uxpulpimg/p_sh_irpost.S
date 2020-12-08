# See LICENSE for license details.

#*****************************************************************************
# p_sh_irpost.S
#-----------------------------------------------------------------------------
#
# Test p.sh (immediate-register post-increment) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_ST_POST_OP( 2, p.sh, lh, 0x000000aa, 0, tdat );
  TEST_ST_POST_OP( 3, p.sh, lh, 0xffffaa00, 2, tdat );
  TEST_ST_POST_OP( 4, p.sh, lw, 0xbeef0aa0, 4, tdat );
  TEST_ST_POST_OP( 5, p.sh, lh, 0xffffa00a, 6, tdat );

  # Negative offset
  TEST_ST_POST_OP( 6, p.sh, lh, 0x000000aa, -6, tdat8 );
  TEST_ST_POST_OP( 7, p.sh, lh, 0xffffaa00, -4, tdat8 );
  TEST_ST_POST_OP( 8, p.sh, lh, 0x00000aa0, -2, tdat8 );
  TEST_ST_POST_OP( 9, p.sh, lh, 0xffffa00a,  0,  tdat8 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_ST_POST_SRC12_BYPASS( 10, 0, 0, p.sh, lh, 0xffffccdd,  0, tdat );
  TEST_ST_POST_SRC12_BYPASS( 11, 0, 1, p.sh, lh, 0xffffbccd,  2, tdat );
  TEST_ST_POST_SRC12_BYPASS( 12, 0, 2, p.sh, lh, 0xffffbbcc,  4, tdat );
  TEST_ST_POST_SRC12_BYPASS( 13, 1, 0, p.sh, lh, 0xffffabbc,  6, tdat );
  TEST_ST_POST_SRC12_BYPASS( 14, 1, 1, p.sh, lh, 0xffffaabb,  8, tdat );
  TEST_ST_POST_SRC12_BYPASS( 15, 2, 0, p.sh, lh, 0xffffdaab, 10, tdat );

  TEST_ST_POST_SRC21_BYPASS( 16, 0, 0, p.sh, lh, 0x00002233,  0, tdat );
  TEST_ST_POST_SRC21_BYPASS( 17, 0, 1, p.sh, lh, 0x00001223,  2, tdat );
  TEST_ST_POST_SRC21_BYPASS( 18, 0, 2, p.sh, lh, 0x00001122,  4, tdat );
  TEST_ST_POST_SRC21_BYPASS( 19, 1, 0, p.sh, lh, 0x00000112,  6, tdat );
  TEST_ST_POST_SRC21_BYPASS( 20, 1, 1, p.sh, lh, 0x00000011,  8, tdat );
  TEST_ST_POST_SRC21_BYPASS( 21, 2, 0, p.sh, lh, 0x00003001, 10, tdat );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat0:  .half 0xbeef
tdat1:  .half 0xbeef
tdat2:  .half 0xbeef
tdat3:  .half 0xbeef
tdat4:  .half 0xbeef
tdat5:  .half 0xbeef
tdat6:  .half 0xbeef
tdat7:  .half 0xbeef
tdat8:  .half 0xbeef
tdat9:  .half 0xbeef

RVTEST_DATA_END
