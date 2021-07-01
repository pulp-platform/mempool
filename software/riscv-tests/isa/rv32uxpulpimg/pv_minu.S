# See LICENSE for license details.

#*****************************************************************************
# pv_minu.S
#-----------------------------------------------------------------------------
#
# Test pv.minu instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.minu.h
  TEST_RR_OP( 2, pv.minu.h, 0x6A212A68, 0xE2B42A68, 0x6A212B4A );
  TEST_RR_OP( 3, pv.minu.h, 0x50AA637D, 0xC219637D, 0x50AA84CC );
  TEST_RR_OP( 4, pv.minu.h, 0x579039EE, 0x92C439EE, 0x5790DCDC );
  # pv.minu.sc.h
  TEST_RR_OP( 5, pv.minu.sc.h, 0x7EF4A8D0, 0x7EF4D67D, 0x268CA8D0 );
  TEST_RR_OP( 6, pv.minu.sc.h, 0x8C9F3E8A, 0x9A9F3E8A, 0x2E6A8C9F );
  TEST_RR_OP( 7, pv.minu.sc.h, 0x844C6178, 0x844C6178, 0x7A819ECF );
  # pv.minu.sci.h
  TEST_UIMM6_OP(  8, pv.minu.sci.h, 0x000B000B, 0x2E8024BF, 11 );
  TEST_UIMM6_OP(  9, pv.minu.sci.h, 0x000B000B, 0x7070C7D7, 11 );
  TEST_UIMM6_OP( 10, pv.minu.sci.h, 0x000B000B, 0x6955494F, 11 );
  # pv.minu.b
  TEST_RR_OP( 11, pv.minu.b, 0x46A4170C, 0x46F51795, 0xAAA4C60C );
  TEST_RR_OP( 12, pv.minu.b, 0xA33FAB2C, 0xA33FAB2C, 0xE140C044 );
  TEST_RR_OP( 13, pv.minu.b, 0x43015111, 0xF49B5111, 0x43018736 );
  # pv.minu.sc.b
  TEST_RR_OP( 14, pv.minu.sc.b, 0x3EB0291F, 0x3EBF291F, 0x909B9AB0 );
  TEST_RR_OP( 15, pv.minu.sc.b, 0x000C0C0C, 0x00555837, 0x7F61610C );
  TEST_RR_OP( 16, pv.minu.sc.b, 0x01010101, 0x47AB06B4, 0x0E0F9001 );
  # pv.minu.sci.b
  TEST_UIMM6_OP( 17, pv.minu.sci.b, 0x0B0B0B0B, 0xBEAF5AAB, 11 );
  TEST_UIMM6_OP( 18, pv.minu.sci.b, 0x0B0B0B0B, 0xDC152410, 11 );
  TEST_UIMM6_OP( 19, pv.minu.sci.b, 0x0B0B0B0B, 0x1DAD56C8, 11 );

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
