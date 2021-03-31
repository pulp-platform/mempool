# See LICENSE for license details.

#*****************************************************************************
# pv_srl.S
#-----------------------------------------------------------------------------
#
# Test pv.srl instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.srl.h
  TEST_RR_OP( 2, pv.srl.h, 0x06030067, 0xC076CE34, 0x00050009 );
  TEST_RR_OP( 3, pv.srl.h, 0x00A40047, 0xA41723DF, 0x00080007 );
  TEST_RR_OP( 4, pv.srl.h, 0x00142A49, 0x52ADA926, 0x000A0002 );
  # pv.srl.sc.h
  TEST_RR_OP( 5, pv.srl.sc.h, 0x1EE01053, 0xF706829F, 0x00080003 );
  TEST_RR_OP( 6, pv.srl.sc.h, 0x00000001, 0x3BC79528, 0x000E000F );
  TEST_RR_OP( 7, pv.srl.sc.h, 0x001001BE, 0x04236F94, 0x000D0006 );
  # pv.srl.sci.h
  TEST_UIMM6_OP(  8, pv.srl.sci.h, 0x00450077, 0x8AA9EF3A, 9 );
  TEST_UIMM6_OP(  9, pv.srl.sci.h, 0x0049006B, 0x93A9D63A, 9 );
  TEST_UIMM6_OP( 10, pv.srl.sci.h, 0x003F0040, 0x7E0D81AF, 9 );
  # pv.srl.b
  TEST_RR_OP( 11, pv.srl.b, 0x030C6A01, 0xFAC8D4F6, 0x06040107 );
  TEST_RR_OP( 12, pv.srl.b, 0x07000105, 0x3F0B94B5, 0x03050705 );
  TEST_RR_OP( 13, pv.srl.b, 0x00311065, 0x29C54065, 0x07020200 );
  # pv.srl.sc.b
  TEST_RR_OP( 14, pv.srl.sc.b, 0x3A37353E, 0x746E6A7C, 0x02010701 );
  TEST_RR_OP( 15, pv.srl.sc.b, 0x0A080A0D, 0xAA82A5D6, 0x01030204 );
  TEST_RR_OP( 16, pv.srl.sc.b, 0x6F5D6D75, 0xDEBBDAEB, 0x03040701 );
  # pv.srl.sci.b
  TEST_UIMM6_OP( 17, pv.srl.sci.b, 0x06010704, 0xCD2DE193, 5 );
  TEST_UIMM6_OP( 18, pv.srl.sci.b, 0x00030507, 0x0B64B9E8, 5 );
  TEST_UIMM6_OP( 19, pv.srl.sci.b, 0x02070306, 0x50E572CB, 5 );

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
