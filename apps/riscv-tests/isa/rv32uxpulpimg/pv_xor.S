# See LICENSE for license details.

#*****************************************************************************
# pv_xor.S
#-----------------------------------------------------------------------------
#
# Test pv.xor instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.xor.h
  TEST_RR_OP( 2, pv.xor.h, 0x66F696DC, 0x5FCE4AD5, 0x3938DC09 );
  TEST_RR_OP( 3, pv.xor.h, 0x58A5BD3D, 0x672A5F61, 0x3F8FE25C );
  TEST_RR_OP( 4, pv.xor.h, 0x339E302C, 0xE468E8F4, 0xD7F6D8D8 );
  # pv.xor.sc.h
  TEST_RR_OP( 5, pv.xor.sc.h, 0x5FB150BC, 0xC4A5CBA8, 0x43CC9B14 );
  TEST_RR_OP( 6, pv.xor.sc.h, 0x48030479, 0xD7F09B8A, 0xCB019FF3 );
  TEST_RR_OP( 7, pv.xor.sc.h, 0x0465D51A, 0x40CF91B0, 0x55DB44AA );
  # pv.xor.sci.h
  TEST_UIMM6_OP(  8, pv.xor.sci.h, 0x0F43E04C, 0x0F48E047, 11 );
  TEST_UIMM6_OP(  9, pv.xor.sci.h, 0xEC22101C, 0xEC291017, 11 );
  TEST_UIMM6_OP( 10, pv.xor.sci.h, 0x137F208C, 0x13742087, 11 );
  # pv.xor.b
  TEST_RR_OP( 11, pv.xor.b, 0x6A9EC5B4, 0x13518603, 0x79CF43B7 );
  TEST_RR_OP( 12, pv.xor.b, 0xEE0CDAEA, 0x59CAB02D, 0xB7C66AC7 );
  TEST_RR_OP( 13, pv.xor.b, 0x5B6E4CC1, 0x8B61A064, 0xD00FECA5 );
  # pv.xor.sc.b
  TEST_RR_OP( 14, pv.xor.sc.b, 0x40CF2054, 0x0F806F1B, 0x7CD0414F );
  TEST_RR_OP( 15, pv.xor.sc.b, 0x89E5AA00, 0x127E319B, 0xC919409B );
  TEST_RR_OP( 16, pv.xor.sc.b, 0xFC7E17F9, 0xAE2C45AB, 0xB9254252 );
  # pv.xor.sci.b
  TEST_UIMM6_OP( 17, pv.xor.sci.b, 0x2D2D131C, 0x26261817, 11 );
  TEST_UIMM6_OP( 18, pv.xor.sci.b, 0x23EC42D8, 0x28E749D3, 11 );
  TEST_UIMM6_OP( 19, pv.xor.sci.b, 0xCAA811C9, 0xC1A31AC2, 11 );

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
