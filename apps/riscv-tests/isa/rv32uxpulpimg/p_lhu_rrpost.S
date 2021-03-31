# See LICENSE for license details.

#*****************************************************************************
# p_lhu_rrpost.S
#-----------------------------------------------------------------------------
#
# Test p.lhu (register-register post-increment) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_LD_RR_POST_OP( 2, p.lhu, 0x000000ff, 0,  tdat )
  TEST_LD_RR_POST_OP( 3, p.lhu, 0x000000ff, 2,  tdat )
  TEST_LD_RR_POST_OP( 4, p.lhu, 0x0000ff00, 4, tdat1 )
  TEST_LD_RR_POST_OP( 5, p.lhu, 0x0000ff00, 6, tdat1 )

  # Negative offset
  TEST_LD_RR_POST_OP( 6, p.lhu, 0x00000ff0, -6, tdat2 )
  TEST_LD_RR_POST_OP( 7, p.lhu, 0x00000ff0, -4, tdat2 )
  TEST_LD_RR_POST_OP( 8, p.lhu, 0x0000f00f, -2, tdat3 )
  TEST_LD_RR_POST_OP( 9, p.lhu, 0x0000f00f,  0, tdat3 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_LD_RR_POST_DEST_BYPASS( 10, 0, p.lhu, 0x000000ff, 2, tdat0 )
  TEST_LD_RR_POST_DEST_BYPASS( 11, 1, p.lhu, 0x0000ff00, 2, tdat1 )
  TEST_LD_RR_POST_DEST_BYPASS( 12, 2, p.lhu, 0x00000ff0, 2, tdat2 )

  TEST_LD_RR_POST_SRC12_BYPASS( 13, 0, 0, p.lhu, 0x000000ff,  2, tdat0 )
  TEST_LD_RR_POST_SRC12_BYPASS( 14, 0, 1, p.lhu, 0x0000f00f, -2, tdat3 )
  TEST_LD_RR_POST_SRC12_BYPASS( 15, 0, 2, p.lhu, 0x00000ff0,  2, tdat2 )
  TEST_LD_RR_POST_SRC12_BYPASS( 16, 1, 0, p.lhu, 0x000000ff,  2, tdat0 )
  TEST_LD_RR_POST_SRC12_BYPASS( 17, 1, 1, p.lhu, 0x0000f00f, -2, tdat3 )
  TEST_LD_RR_POST_SRC12_BYPASS( 18, 2, 0, p.lhu, 0x00000ff0,  2, tdat2 )

  TEST_LD_RR_POST_SRC21_BYPASS( 19, 0, 0, p.lhu, 0x000000ff,  2, tdat0 )
  TEST_LD_RR_POST_SRC21_BYPASS( 20, 0, 1, p.lhu, 0x0000f00f, -2, tdat3 )
  TEST_LD_RR_POST_SRC21_BYPASS( 21, 0, 2, p.lhu, 0x00000ff0,  2, tdat2 )
  TEST_LD_RR_POST_SRC21_BYPASS( 22, 1, 0, p.lhu, 0x000000ff,  2, tdat0 )
  TEST_LD_RR_POST_SRC21_BYPASS( 23, 1, 1, p.lhu, 0x0000f00f, -2, tdat3 )
  TEST_LD_RR_POST_SRC21_BYPASS( 24, 2, 0, p.lhu, 0x00000ff0,  2, tdat2 )

  #-------------------------------------------------------------
  # Test write-after-write hazard
  #-------------------------------------------------------------

  TEST_LD_RR_POST_DEST1_WAW( 25, p.lhu,  25, tdat )
  TEST_LD_RR_POST_DEST1_WAW( 26, p.lhu, -76, tdat )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat0:  .half 0x00ff
tdat1:  .half 0xff00
tdat2:  .half 0x0ff0
tdat3:  .half 0xf00f

RVTEST_DATA_END
