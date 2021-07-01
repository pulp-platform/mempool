# See LICENSE for license details.

#*****************************************************************************
# pv_dotup.S
#-----------------------------------------------------------------------------
#
# Test pv.dotup instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.dotup.h
  TEST_RR_OP( 2, pv.dotup.h, 0x2A78A592, 0xFE67FB1A, 0x50E4DE57 );
  TEST_RR_OP( 3, pv.dotup.h, 0x6F4A3DAA, 0xADBC1E09, 0xA2C806FA );
  TEST_RR_OP( 4, pv.dotup.h, 0xDD21210B, 0x3FDAEFE7, 0x7BA5CB0F );
  # pv.dotup.sc.h
  TEST_RR_OP( 5, pv.dotup.sc.h, 0x6E59BCF3, 0x5E5C31BF, 0xCB24C409 );
  TEST_RR_OP( 6, pv.dotup.sc.h, 0x4A884EE4, 0xEC042250, 0x230A4695 );
  TEST_RR_OP( 7, pv.dotup.sc.h, 0x176809E6, 0x6BF5D085, 0x9AB012EF );
  # pv.dotup.sci.h
  TEST_UIMM6_OP(  8, pv.dotup.sci.h, 0x00148D3C, 0x36D2FEAA, 17 );
  TEST_UIMM6_OP(  9, pv.dotup.sci.h, 0x0002CC3A, 0x6752FECB,  2 );
  TEST_UIMM6_OP( 10, pv.dotup.sci.h, 0x000F6F94, 0x9747CFF5, 11 );
  # pv.dotup.b
  TEST_RR_OP( 11, pv.dotup.b, 0x0001DADA, 0xEB8A58F5, 0xCAECEE54 );
  TEST_RR_OP( 12, pv.dotup.b, 0x0000B305, 0x47665939, 0x9E989665 );
  TEST_RR_OP( 13, pv.dotup.b, 0x0000D535, 0x79D072B4, 0x5B8B4327 );
  # pv.dotup.sc.b
  TEST_RR_OP( 14, pv.dotup.sc.b, 0x000059EF, 0x6F622436, 0x1E1E694D );
  TEST_RR_OP( 15, pv.dotup.sc.b, 0x000101DA, 0x77B8759A, 0xC1056E73 );
  TEST_RR_OP( 16, pv.dotup.sc.b, 0x00002238, 0x74740933, 0xF898DF1E );
  # pv.dotup.sci.b
  TEST_UIMM6_OP( 17, pv.dotup.sci.b, 0x00000FBA, 0x4CD92920, 11 );
  TEST_UIMM6_OP( 18, pv.dotup.sci.b, 0x00002140, 0xAFCE7172, 14 );
  TEST_UIMM6_OP( 19, pv.dotup.sci.b, 0x00001053, 0xDB25ABAA,  7 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_SRC1_EQ_DEST,
  # TEST_RR_SRC2_EQ_DEST, TEST_RR_SRC12_EQ_DEST
  # for register-uimm6 instructions TEST_UIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_DEST_BYPASS,
  # TEST_RR_SRC12_BYPASS, TEST_RR_SRC21_BYPASS, TEST_RR_ZEROSRC1,
  # TEST_RR_ZEROSRC2, TEST_RR_ZEROSRC12, TEST_RR_ZERODEST
  # for register-uimm6 instructions TEST_UIMM6_DEST_BYPASS,
  # TEST_UIMM6_SRC1_BYPASS, TEST_UIMM6_ZEROSRC1, TEST_UIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
