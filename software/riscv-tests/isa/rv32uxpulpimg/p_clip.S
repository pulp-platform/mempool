# See LICENSE for license details.

#*****************************************************************************
# p_clip.S
#-----------------------------------------------------------------------------
#
# Test p.clip instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

    #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_UIMM5_OP( 2,  p.clip, 0x00000000, 0x00000000, 0x00 );
  TEST_UIMM5_OP( 3,  p.clip, 0xffffffff, 0xffffffff, 0x00 );
  TEST_UIMM5_OP( 4,  p.clip, 0x00000000, 0x00000000, 0x1f );
  TEST_UIMM5_OP( 5,  p.clip, 0xffffffff, 0xffffffff, 0x1f );

  TEST_UIMM5_OP( 6,  p.clip, 0xfffffc00, 0x8fffab52, 0x0b ); # rs1 < -2^(imm5-1)
  TEST_UIMM5_OP( 7,  p.clip, 0xfffffc00, 0xfffffc00, 0x1d ); # rs1 = -2^(imm5-1)
  TEST_UIMM5_OP( 8,  p.clip, 0x00000a03, 0x00000a03, 0x0f ); # -2^(imm5-1) < rs1 < 2^(imm5-1)-1
  TEST_UIMM5_OP( 9,  p.clip, 0x00003fff, 0x00003fff, 0x0f ); # rs1 = 2^(imm5-1)-1
  TEST_UIMM5_OP( 10, p.clip, 0x00000007, 0x0Bcd0015, 0x04 ); # rs1 > 2^(imm5-1)-1

  TEST_UIMM5_OP( 11, p.clip, 0xffffffff, 0xfffffffe, 0x00 ); # test -2^(imm5-1) = -1 when imm5 = 0
  TEST_UIMM5_OP( 12, p.clip, 0xffffffff, 0x8f00000e, 0x00 ); # test -2^(imm5-1) = -1 when imm5 = 0
  TEST_UIMM5_OP( 13, p.clip, 0x00000000, 0x00000001, 0x00 ); # test 2^(imm5-1)-1 = 0 when imm5 = 0
  TEST_UIMM5_OP( 14, p.clip, 0x00000000, 0x0fff8cbd, 0x00 ); # test 2^(imm5-1)-1 = 0 when imm5 = 0

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_UIMM5_SRC1_EQ_DEST( 15, p.clip, 13, 13, 11 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_UIMM5_DEST_BYPASS( 16, 0, p.clip,  -1,  -1, 2 );
  TEST_UIMM5_DEST_BYPASS( 17, 1, p.clip,   3,  30, 3 );
  TEST_UIMM5_DEST_BYPASS( 18, 2, p.clip, 100, 100, 8 );

  TEST_UIMM5_SRC1_BYPASS( 19, 0, p.clip,  -1,  -1, 2 );
  TEST_UIMM5_SRC1_BYPASS( 20, 1, p.clip,   3,  30, 3 );
  TEST_UIMM5_SRC1_BYPASS( 21, 2, p.clip, 100, 100, 8 );

  TEST_UIMM5_ZEROSRC1( 22, p.clip, 0, 16 );
  TEST_UIMM5_ZERODEST( 23, p.clip, 33, 7 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
