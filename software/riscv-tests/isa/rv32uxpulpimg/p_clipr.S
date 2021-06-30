# See LICENSE for license details.

#*****************************************************************************
# p_clipr.S
#-----------------------------------------------------------------------------
#
# Test p.clipr instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.clipr, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.clipr, 0x00000000, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.clipr, 0xffffffff, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.clipr, 0x00000000, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.clipr, 0xffff2e06, 0xfad00011, 0x0000d1f9 ); # rs2 > 0, rs1 < -(rs2+1)
  TEST_RR_OP( 7, p.clipr, 0xffff2e06, 0xffff2e06, 0x0000d1f9 ); # rs2 > 0, rs1 = -(rs2+1)
  TEST_RR_OP( 8, p.clipr, 0xfff55bb6, 0xfff55bb6, 0x0010fd29 ); # rs2 > 0, -(rs2+1) < rs1 < rs2
  TEST_RR_OP( 9, p.clipr, 0x0010fd29, 0x0010fd29, 0x0010fd29 ); # rs2 > 0, rs1 = rs2
  TEST_RR_OP( 10, p.clipr, 0x0010fd29, 0x0ff55bb6, 0x0010fd29 ); # rs2 > 0, rs1 > rs2

  TEST_RR_OP( 11, p.clipr, 0x020ff639, 0x8019d1f9, 0xfDf009c6 ); # rs2 < 0, rs1 < rs2
  TEST_RR_OP( 12, p.clipr, 0x020ff639, 0xfDf009c6, 0xfDf009c6 ); # rs2 < 0, rs1 = rs2
  TEST_RR_OP( 13, p.clipr, 0x0f0ff639, 0x0019d1f9, 0xf0f009c6 ); # rs2 < 0, rs2 < rs1 < -(rs2+1)
  TEST_RR_OP( 14, p.clipr, 0x0f0ff639, 0x0f0ff639, 0xf0f009c6 ); # rs2 < 0, rs1 = -(rs2+1)
  TEST_RR_OP( 15, p.clipr, 0xfffffAC6, 0x00A00B0C, 0xfffffAC6 ); # rs2 < 0, rs1 > -(rs2+1)

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 16, p.clipr, 50, 50, 51);
  TEST_RR_SRC2_EQ_DEST( 17, p.clipr, -7, 210, -7);

  TEST_RR_SRC12_EQ_DEST( 18, p.clipr, 101, 101 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 19, 0, p.clipr, 11, 53, 11 );
  TEST_RR_DEST_BYPASS( 20, 1, p.clipr, 71, 11, -72);
  TEST_RR_DEST_BYPASS( 21, 2, p.clipr, 11, 15, 11 );

  TEST_RR_SRC12_BYPASS( 22, 0, 0, p.clipr, 11, 13, 11);
  TEST_RR_SRC12_BYPASS( 23, 0, 1, p.clipr, 11, 14, 11);
  TEST_RR_SRC12_BYPASS( 24, 0, 2, p.clipr, 11, 15, 11);
  TEST_RR_SRC12_BYPASS( 25, 1, 0, p.clipr, 11, 13, 11);
  TEST_RR_SRC12_BYPASS( 26, 1, 1, p.clipr, 11, 14, 11);
  TEST_RR_SRC12_BYPASS( 27, 2, 0, p.clipr, 11, 15, 11);

  TEST_RR_SRC21_BYPASS( 28, 0, 0, p.clipr, 11, 13, 11);
  TEST_RR_SRC21_BYPASS( 29, 0, 1, p.clipr, 11, 14, 11);
  TEST_RR_SRC21_BYPASS( 30, 0, 2, p.clipr, 11, 15, 11);
  TEST_RR_SRC21_BYPASS( 31, 1, 0, p.clipr, 11, 13, 11);
  TEST_RR_SRC21_BYPASS( 32, 1, 1, p.clipr, 11, 14, 11);
  TEST_RR_SRC21_BYPASS( 33, 2, 0, p.clipr, 11, 15, 11);

  TEST_RR_ZEROSRC1( 34, p.clipr, 0, 15 );
  TEST_RR_ZEROSRC2( 35, p.clipr, -1, -32 );
  TEST_RR_ZEROSRC12( 36, p.clipr, 0 );

  TEST_RR_ZERODEST( 37, p.clipr, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
