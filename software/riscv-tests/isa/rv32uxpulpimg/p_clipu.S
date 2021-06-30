# See LICENSE for license details.

#*****************************************************************************
# p_clipu.S
#-----------------------------------------------------------------------------
#
# Test p.clipu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_UIMM5_OP( 2,  p.clipu, 0x00000000, 0x00000000, 0x00 );
  TEST_UIMM5_OP( 3,  p.clipu, 0x00000000, 0xffffffff, 0x00 );
  TEST_UIMM5_OP( 4,  p.clipu, 0x00000000, 0x00000000, 0x1f );
  TEST_UIMM5_OP( 5,  p.clipu, 0x00000000, 0xffffffff, 0x1f );

  TEST_UIMM5_OP( 6,  p.clipu, 0x00000000, 0x8fffab52, 0x0b ); # rs1 < 0
  TEST_UIMM5_OP( 7,  p.clipu, 0x00000000, 0xfffffc00, 0x1d ); # rs1 = 0
  TEST_UIMM5_OP( 8,  p.clipu, 0x00000a03, 0x00000a03, 0x0f ); # 0 < rs1 < 2^(imm5-1)-1
  TEST_UIMM5_OP( 9,  p.clipu, 0x00003fff, 0x00003fff, 0x0f ); # rs1 = 2^(imm5-1)-1
  TEST_UIMM5_OP( 10, p.clipu, 0x00000007, 0x0Bcd0015, 0x04 ); # rs1 > 2^(imm5-1)-1

  TEST_UIMM5_OP( 11, p.clipu, 0x00000000, 0x00000001, 0x00 ); # test 2^(imm5-1)-1 = 0 when imm5 = 0
  TEST_UIMM5_OP( 12, p.clipu, 0x00000000, 0x0fff8cbd, 0x00 ); # test 2^(imm5-1)-1 = 0 when imm5 = 0

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_UIMM5_SRC1_EQ_DEST( 13, p.clipu, 13, 13, 11 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_UIMM5_DEST_BYPASS( 14, 0, p.clipu,   0,  -1, 2 );
  TEST_UIMM5_DEST_BYPASS( 15, 1, p.clipu,   3,  30, 3 );
  TEST_UIMM5_DEST_BYPASS( 16, 2, p.clipu, 100, 100, 8 );

  TEST_UIMM5_SRC1_BYPASS( 17, 0, p.clipu,   0,  -1, 2 );
  TEST_UIMM5_SRC1_BYPASS( 18, 1, p.clipu,   3,  30, 3 );
  TEST_UIMM5_SRC1_BYPASS( 19, 2, p.clipu, 100, 100, 8 );

  TEST_UIMM5_ZEROSRC1( 20, p.clipu, 0, 16 );
  TEST_UIMM5_ZERODEST( 21, p.clipu, 33, 7 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
