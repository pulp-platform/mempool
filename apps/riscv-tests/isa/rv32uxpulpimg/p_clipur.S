# See LICENSE for license details.

#*****************************************************************************
# p_clipur.S
#-----------------------------------------------------------------------------
#
# Test p.clipur instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.clipur, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.clipur, 0x00000000, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.clipur, 0x00000000, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.clipur, 0x00000000, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.clipur,  0x00000000, 0xfad00011, 0x0000d1f9 ); # rs2 > 0, rs1 < 0
  TEST_RR_OP( 7, p.clipur,  0x00000000, 0x00000000, 0x0000d1f9 ); # rs2 > 0, rs1 = 0
  TEST_RR_OP( 8, p.clipur,  0x00015bb6, 0x00015bb6, 0x0010fd29 ); # rs2 > 0, 0 < rs1 < rs2
  TEST_RR_OP( 9, p.clipur,  0x0010fd29, 0x0010fd29, 0x0010fd29 ); # rs2 > 0, rs1 = rs2
  TEST_RR_OP( 10, p.clipur, 0x0010fd29, 0x7010fd29, 0x0010fd29 ); # rs2 > 0, rs1 > rs2

  TEST_RR_OP( 11, p.clipur, 0x00000000, 0x8002d1f9, 0xfDf009c6 ); # rs2 < 0, rs1 < rs2
  TEST_RR_OP( 12, p.clipur, 0x00000000, 0xfDf009c6, 0xfDf009c6 ); # rs2 < 0, rs1 = rs2
  TEST_RR_OP( 13, p.clipur, 0x00000000, 0xf8f0A0c6, 0xf0f009c6 ); # rs2 < 0, rs2 < rs1 < 0
  TEST_RR_OP( 14, p.clipur, 0x00000000, 0x00000000, 0x87f010bc ); # rs2 < 0, rs1 = 0
  TEST_RR_OP( 15, p.clipur, 0x87f010bc, 0x00A00B0C, 0x87f010bc ); # rs2 < 0, rs1 > 0

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 16, p.clipur, 16, 16, 51);
  TEST_RR_SRC2_EQ_DEST( 17, p.clipur, -7, 210, -7);

  TEST_RR_SRC12_EQ_DEST( 18, p.clipur, 101, 101 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 19, 0, p.clipur, 11, 53, 11 );
  TEST_RR_DEST_BYPASS( 20, 1, p.clipur, -72, 11, -72);
  TEST_RR_DEST_BYPASS( 21, 2, p.clipur, 11, 15, 11 );

  TEST_RR_SRC12_BYPASS( 22, 0, 0, p.clipur, 11, 13, 11);
  TEST_RR_SRC12_BYPASS( 23, 0, 1, p.clipur, 11, 14, 11);
  TEST_RR_SRC12_BYPASS( 24, 0, 2, p.clipur, 11, 15, 11);
  TEST_RR_SRC12_BYPASS( 25, 1, 0, p.clipur, 11, 13, 11);
  TEST_RR_SRC12_BYPASS( 26, 1, 1, p.clipur, 11, 14, 11);
  TEST_RR_SRC12_BYPASS( 27, 2, 0, p.clipur, 11, 15, 11);

  TEST_RR_SRC21_BYPASS( 28, 0, 0, p.clipur, 11, 13, 11);
  TEST_RR_SRC21_BYPASS( 29, 0, 1, p.clipur, 11, 14, 11);
  TEST_RR_SRC21_BYPASS( 30, 0, 2, p.clipur, 11, 15, 11);
  TEST_RR_SRC21_BYPASS( 31, 1, 0, p.clipur, 11, 13, 11);
  TEST_RR_SRC21_BYPASS( 32, 1, 1, p.clipur, 11, 14, 11);
  TEST_RR_SRC21_BYPASS( 33, 2, 0, p.clipur, 11, 15, 11);

  TEST_RR_ZEROSRC1( 34, p.clipur, 0, 15);
  TEST_RR_ZEROSRC2( 35, p.clipur, 0, -32);
  TEST_RR_ZEROSRC12( 36, p.clipur, 0 );

  TEST_RR_ZERODEST( 37, p.clipur, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
