# See LICENSE for license details.

#*****************************************************************************
# p_lbu_rrpost.S
#-----------------------------------------------------------------------------
#
# Test p.lbu (register-register post-increment) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_LD_RR_POST_OP( 2, p.lbu, 0x000000ff, 0,  tdat )
  TEST_LD_RR_POST_OP( 3, p.lbu, 0x000000ff, 1,  tdat )
  TEST_LD_RR_POST_OP( 4, p.lbu, 0x0000000f, 2, tdat3 )
  TEST_LD_RR_POST_OP( 5, p.lbu, 0x0000000f, 3, tdat3 )

  # Negative offset
  TEST_LD_RR_POST_OP( 6, p.lbu, 0x00000000, -3, tdat1 )
  TEST_LD_RR_POST_OP( 7, p.lbu, 0x00000000, -2, tdat1 )
  TEST_LD_RR_POST_OP( 8, p.lbu, 0x000000f0, -1, tdat2 )
  TEST_LD_RR_POST_OP( 9, p.lbu, 0x000000f0,  0, tdat2 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_LD_RR_POST_DEST_BYPASS( 10, 0, p.lbu, 0x000000ff, 1, tdat0 )
  TEST_LD_RR_POST_DEST_BYPASS( 11, 1, p.lbu, 0x00000000, 1, tdat1 )
  TEST_LD_RR_POST_DEST_BYPASS( 12, 2, p.lbu, 0x000000f0, 1, tdat2 )

  TEST_LD_RR_POST_SRC12_BYPASS( 13, 0, 0, p.lbu, 0x000000ff,  1, tdat0 )
  TEST_LD_RR_POST_SRC12_BYPASS( 14, 0, 1, p.lbu, 0x0000000f, -1, tdat3 )
  TEST_LD_RR_POST_SRC12_BYPASS( 15, 0, 2, p.lbu, 0x000000f0,  1, tdat2 )
  TEST_LD_RR_POST_SRC12_BYPASS( 16, 1, 0, p.lbu, 0x000000ff,  1, tdat0 )
  TEST_LD_RR_POST_SRC12_BYPASS( 17, 1, 1, p.lbu, 0x0000000f, -1, tdat3 )
  TEST_LD_RR_POST_SRC12_BYPASS( 18, 2, 0, p.lbu, 0x000000f0,  1, tdat2 )

  TEST_LD_RR_POST_SRC21_BYPASS( 19, 0, 0, p.lbu, 0x000000ff,  1, tdat0 )
  TEST_LD_RR_POST_SRC21_BYPASS( 20, 0, 1, p.lbu, 0x0000000f, -1, tdat3 )
  TEST_LD_RR_POST_SRC21_BYPASS( 21, 0, 2, p.lbu, 0x000000f0,  1, tdat2 )
  TEST_LD_RR_POST_SRC21_BYPASS( 22, 1, 0, p.lbu, 0x000000ff,  1, tdat0 )
  TEST_LD_RR_POST_SRC21_BYPASS( 23, 1, 1, p.lbu, 0x0000000f, -1, tdat3 )
  TEST_LD_RR_POST_SRC21_BYPASS( 24, 2, 0, p.lbu, 0x000000f0,  1, tdat2 )

  #-------------------------------------------------------------
  # Test write-after-write hazard
  #-------------------------------------------------------------

  TEST_LD_RR_POST_DEST1_WAW( 25, p.lbu,  25, tdat )
  TEST_LD_RR_POST_DEST1_WAW( 26, p.lbu, -76, tdat )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat0:  .byte 0xff
tdat1:  .byte 0x00
tdat2:  .byte 0xf0
tdat3:  .byte 0x0f

RVTEST_DATA_END
