# See LICENSE for license details.

#*****************************************************************************
# p_lh_irpost.S
#-----------------------------------------------------------------------------
#
# Test p.lh (immediate-register post-increment) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_LD_POST_OP( 2, p.lh, 0x000000ff, 0,  tdat )
  TEST_LD_POST_OP( 3, p.lh, 0x000000ff, 2,  tdat )
  TEST_LD_POST_OP( 4, p.lh, 0xfffff00f, 4, tdat3 )
  TEST_LD_POST_OP( 5, p.lh, 0xfffff00f, 6, tdat3 )

  # Negative offset
  TEST_LD_POST_OP( 6, p.lh, 0xffffff00, -6, tdat1 )
  TEST_LD_POST_OP( 7, p.lh, 0xffffff00, -4, tdat1 )
  TEST_LD_POST_OP( 8, p.lh, 0x00000ff0, -2, tdat2 )
  TEST_LD_POST_OP( 9, p.lh, 0x00000ff0,  0, tdat2 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_LD_POST_DEST1_BYPASS( 10, 0, p.lh, 0x000000ff, 2, tdat0 )
  TEST_LD_POST_DEST1_BYPASS( 11, 1, p.lh, 0xffffff00, 2, tdat1 )
  TEST_LD_POST_DEST1_BYPASS( 12, 2, p.lh, 0x00000ff0, 2, tdat2 )

  TEST_LD_POST_DEST2_BYPASS( 13, 0, p.lh,  4, tdat0 )
  TEST_LD_POST_DEST2_BYPASS( 14, 1, p.lh,  2, tdat1 )
  TEST_LD_POST_DEST2_BYPASS( 15, 2, p.lh, -6, tdat3 )

  TEST_LD_POST_SRC1_BYPASS( 16, 0, p.lh, 0x000000ff,  2, tdat0 )
  TEST_LD_POST_SRC1_BYPASS( 17, 1, p.lh, 0xfffff00f, -2, tdat3 )
  TEST_LD_POST_SRC1_BYPASS( 18, 2, p.lh, 0x00000ff0,  2, tdat2 )

  #-------------------------------------------------------------
  # Test write-after-write hazard
  #-------------------------------------------------------------

  TEST_LD_POST_DEST1_WAW( 19, p.lh,  25, tdat )
  TEST_LD_POST_DEST1_WAW( 20, p.lh, -76, tdat )

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
