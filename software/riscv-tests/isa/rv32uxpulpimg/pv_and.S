# See LICENSE for license details.

#*****************************************************************************
# pv_and.S
#-----------------------------------------------------------------------------
#
# Test pv.and instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.and.h
  TEST_RR_OP( 2, pv.and.h, 0xE1C028D0, 0xE1D16DD8, 0xE7E4A8F0 );
  TEST_RR_OP( 3, pv.and.h, 0x30111070, 0xB0111070, 0x3715D975 );
  TEST_RR_OP( 4, pv.and.h, 0x04000084, 0x04040AA4, 0xBD7314C7 );
  # pv.and.sc.h
  TEST_RR_OP( 5, pv.and.sc.h, 0x18008480, 0x5818A5AB, 0x7C269E80 );
  TEST_RR_OP( 6, pv.and.sc.h, 0x0E0B0683, 0xCF2B6697, 0x4E211ECB );
  TEST_RR_OP( 7, pv.and.sc.h, 0x08070806, 0x28376966, 0xD7848E0F );
  # pv.and.sci.h
  TEST_UIMM6_OP(  8, pv.and.sci.h, 0x00010003, 0xBFE568E7, 11 );
  TEST_UIMM6_OP(  9, pv.and.sci.h, 0x000A0001, 0xC08A6275, 11 );
  TEST_UIMM6_OP( 10, pv.and.sci.h, 0x000A0008, 0xDFEE3E6C, 11 );
  # pv.and.b
  TEST_RR_OP( 11, pv.and.b, 0xA106671C, 0xE317675C, 0xADC6E7BF );
  TEST_RR_OP( 12, pv.and.b, 0x036080A8, 0xB360A0A8, 0x077A84AC );
  TEST_RR_OP( 13, pv.and.b, 0x0B430011, 0x1FDB225B, 0xCB431CB5 );
  # pv.and.sc.b
  TEST_RR_OP( 14, pv.and.sc.b, 0xE4892568, 0xE48B3778, 0xCCC46AED );
  TEST_RR_OP( 15, pv.and.sc.b, 0x00000000, 0x0D96B284, 0x8B596F00 );
  TEST_RR_OP( 16, pv.and.sc.b, 0x49672C2F, 0xC9672CBF, 0x6AC7706F );
  # pv.and.sci.b
  TEST_UIMM6_OP( 17, pv.and.sci.b, 0x0B090808, 0x8F29C848, 11 );
  TEST_UIMM6_OP( 18, pv.and.sci.b, 0x000A0908, 0x30EA9D78, 11 );
  TEST_UIMM6_OP( 19, pv.and.sci.b, 0x03000801, 0x83743C41, 11 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_SRC1_EQ_DEST,
  # TEST_RR_SRC2_EQ_DEST, TEST_RR_SRC12_EQ_DEST
  # for register-simm6 instructions TEST_UIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_DEST_BYPASS,
  # TEST_RR_SRC12_BYPASS, TEST_RR_SRC21_BYPASS, TEST_RR_ZEROSRC1,
  # TEST_RR_ZEROSRC2, TEST_RR_ZEROSRC12, TEST_RR_ZERODEST
  # for register-simm6 instructions TEST_UIMM6_DEST_BYPASS,
  # TEST_UIMM6_SRC1_BYPASS, TEST_UIMM6_ZEROSRC1, TEST_UIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
