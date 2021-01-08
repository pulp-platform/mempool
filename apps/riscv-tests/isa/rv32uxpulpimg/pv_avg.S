# See LICENSE for license details.

#*****************************************************************************
# pv_avg.S
#-----------------------------------------------------------------------------
#
# Test pv.avg instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.avg.h
  TEST_RR_OP( 2, pv.avg.h, 0xDFA53D57, 0x2C5F4D25, 0x92EC2D89 );
  TEST_RR_OP( 3, pv.avg.h, 0x18A2C49C, 0xD09FBFB6, 0x60A5C983 );
  TEST_RR_OP( 4, pv.avg.h, 0xD290A560, 0xE37F8F8F, 0xC1A2BB32 );
  # pv.avg.sc.h
  TEST_RR_OP( 5, pv.avg.sc.h, 0xF8B0DF51, 0x6A263768, 0xD18D873A );
  TEST_RR_OP( 6, pv.avg.sc.h, 0x29B50628, 0xDA3A9320, 0xDB667930 );
  TEST_RR_OP( 7, pv.avg.sc.h, 0x1CBDF112, 0x4376EC20, 0x13B2F605 );
  # pv.avg.sci.h
  TEST_SIMM6_OP(  8, pv.avg.sci.h, 0x2F8BD535, 0x5F0CAA60, 11 );
  TEST_SIMM6_OP(  9, pv.avg.sci.h, 0x1F1B0A1B, 0x3E2B142C, 11 );
  TEST_SIMM6_OP( 10, pv.avg.sci.h, 0x1E533C46, 0x3C9C7881, 11 );
  # pv.avg.b
  TEST_RR_OP( 11, pv.avg.b, 0xEF09DD01, 0x242B76A4, 0xBBE7445F );
  TEST_RR_OP( 12, pv.avg.b, 0x2C31DBEE, 0x7B0B5CD3, 0xDE575B0A );
  TEST_RR_OP( 13, pv.avg.b, 0xF11E19E0, 0x0278F0DE, 0xE0C543E3 );
  # pv.avg.sc.b
  TEST_RR_OP( 14, pv.avg.sc.b, 0x12E71EFC, 0x40E95813, 0xDE5394E5 );
  TEST_RR_OP( 15, pv.avg.sc.b, 0x102204DA, 0xE005C975, 0xE6677040 );
  TEST_RR_OP( 16, pv.avg.sc.b, 0x1E2ADA29, 0x2840A03D, 0xCF897515 );
  # pv.avg.sci.b
  TEST_SIMM6_OP( 17, pv.avg.sci.b, 0x04D5DEFE, 0xFDA0B1F1, 11 );
  TEST_SIMM6_OP( 18, pv.avg.sci.b, 0xD4192A1E, 0x9E274932, 11 );
  TEST_SIMM6_OP( 19, pv.avg.sci.b, 0x11E3CFE6, 0x17BC93C1, 11 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_SRC1_EQ_DEST,
  # TEST_RR_SRC2_EQ_DEST, TEST_RR_SRC12_EQ_DEST
  # for register-simm6 instructions TEST_SIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_DEST_BYPASS,
  # TEST_RR_SRC12_BYPASS, TEST_RR_SRC21_BYPASS, TEST_RR_ZEROSRC1,
  # TEST_RR_ZEROSRC2, TEST_RR_ZEROSRC12, TEST_RR_ZERODEST
  # for register-simm6 instructions TEST_SIMM6_DEST_BYPASS,
  # TEST_SIMM6_SRC1_BYPASS, TEST_SIMM6_ZEROSRC1, TEST_SIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
