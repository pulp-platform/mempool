# See LICENSE for license details.

#*****************************************************************************
# pv_sub.S
#-----------------------------------------------------------------------------
#
# Test pv.sub instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.sub.h
  TEST_RR_OP( 2, pv.sub.h, 0x21549541, 0xC037A04F, 0x9EE30B0E );
  TEST_RR_OP( 3, pv.sub.h, 0x0A8F87AF, 0xA6011B6C, 0x9B7293BD );
  TEST_RR_OP( 4, pv.sub.h, 0xE3DFCB44, 0x2BD6C73C, 0x47F7FBF8 );
  # pv.sub.sc.h
  TEST_RR_OP( 5, pv.sub.sc.h, 0x005D10C7, 0xA7DFB849, 0xA0DAA782 );
  TEST_RR_OP( 6, pv.sub.sc.h, 0x915182F6, 0xEB54DCF9, 0xE0AB5A03 );
  TEST_RR_OP( 7, pv.sub.sc.h, 0x8ADB0963, 0xC72645AE, 0x44033C4B );
  # pv.sub.sci.h
  TEST_SIMM6_OP(  8, pv.sub.sci.h, 0x5F6A01D4, 0x5F7501DF, 11 );
  TEST_SIMM6_OP(  9, pv.sub.sci.h, 0xEDEBEE05, 0xEDF6EE10, 11 );
  TEST_SIMM6_OP( 10, pv.sub.sci.h, 0x5254F633, 0x525FF63E, 11 );
  # pv.sub.b
  TEST_RR_OP( 11, pv.sub.b, 0xCFA312C4, 0xD6B51AA7, 0x071208E3 );
  TEST_RR_OP( 12, pv.sub.b, 0x399B9FC4, 0x273CF552, 0xEEA1568E );
  TEST_RR_OP( 13, pv.sub.b, 0x75B1BB23, 0x3E6DD37D, 0xC9BC185A );
  # pv.sub.sc.b
  TEST_RR_OP( 14, pv.sub.sc.b, 0x85D1880A, 0xCE1AD153, 0x11D9D249 );
  TEST_RR_OP( 15, pv.sub.sc.b, 0xF53BE607, 0xB0F6A1C2, 0xA4990EBB );
  TEST_RR_OP( 16, pv.sub.sc.b, 0xB890FAF0, 0x4A228C82, 0x3DEA1692 );
  # pv.sub.sci.b
  TEST_SIMM6_OP( 17, pv.sub.sci.b, 0x5282B987, 0x5D8DC492, 11 );
  TEST_SIMM6_OP( 18, pv.sub.sci.b, 0x12D59C9F, 0x1DE0A7AA, 11 );
  TEST_SIMM6_OP( 19, pv.sub.sci.b, 0x6C6D5D05, 0x77786810, 11 );

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
