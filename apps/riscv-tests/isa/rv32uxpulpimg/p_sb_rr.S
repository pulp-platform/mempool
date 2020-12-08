# See LICENSE for license details.

#*****************************************************************************
# p_sb_rr.S
#-----------------------------------------------------------------------------
#
# Test p.sb (register-register) instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Basic tests
  #-------------------------------------------------------------

  # Positive offset
  TEST_ST_RR_OP( 2, p.sb, lb, 0xffffffaa, 0, tdat )
  TEST_ST_RR_OP( 3, p.sb, lb, 0x00000000, 1, tdat )
  TEST_ST_RR_OP( 4, p.sb, lh, 0xffffefa0, 2, tdat )
  TEST_ST_RR_OP( 5, p.sb, lb, 0x0000000a, 3, tdat )

  # Negative offset
  TEST_ST_RR_OP( 6, p.sb, lb, 0xffffffaa, -6, tdat8 )
  TEST_ST_RR_OP( 7, p.sb, lb, 0x00000000, -5, tdat8 )
  TEST_ST_RR_OP( 8, p.sb, lb, 0xffffffa0, -3, tdat8 )
  TEST_ST_RR_OP( 9, p.sb, lb, 0x0000000a, -1, tdat8 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_ST_RR_SRC12_BYPASS( 10, 0, 0, p.sb, lb, 0xffffffdd, 0, tdat );
  TEST_ST_RR_SRC12_BYPASS( 11, 0, 1, p.sb, lb, 0xffffffcd, 1, tdat );
  TEST_ST_RR_SRC12_BYPASS( 12, 0, 2, p.sb, lb, 0xffffffcc, 2, tdat );
  TEST_ST_RR_SRC12_BYPASS( 13, 1, 0, p.sb, lb, 0xffffffbc, 3, tdat );
  TEST_ST_RR_SRC12_BYPASS( 14, 1, 1, p.sb, lb, 0xffffffbb, 4, tdat );
  TEST_ST_RR_SRC12_BYPASS( 15, 2, 0, p.sb, lb, 0xffffffab, 5, tdat );

  TEST_ST_RR_SRC21_BYPASS( 16, 0, 0, p.sb, lb, 0x00000033, 0, tdat );
  TEST_ST_RR_SRC21_BYPASS( 17, 0, 1, p.sb, lb, 0x00000023, 1, tdat );
  TEST_ST_RR_SRC21_BYPASS( 18, 0, 2, p.sb, lb, 0x00000022, 2, tdat );
  TEST_ST_RR_SRC21_BYPASS( 19, 1, 0, p.sb, lb, 0x00000012, 3, tdat );
  TEST_ST_RR_SRC21_BYPASS( 20, 1, 1, p.sb, lb, 0x00000011, 4, tdat );
  TEST_ST_RR_SRC21_BYPASS( 21, 2, 0, p.sb, lb, 0x00000001, 5, tdat );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

tdat:
tdat0:  .byte 0xef
tdat1:  .byte 0xef
tdat2:  .byte 0xef
tdat3:  .byte 0xef
tdat4:  .byte 0xef
tdat5:  .byte 0xef
tdat6:  .byte 0xef
tdat7:  .byte 0xef
tdat8:  .byte 0xef
tdat9:  .byte 0xef

RVTEST_DATA_END
