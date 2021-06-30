# See LICENSE for license details.

#*****************************************************************************
# pv_add.S
#-----------------------------------------------------------------------------
#
# Test pv.add instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.add.h
  TEST_RR_OP( 2, pv.add.h, 0xC1ACF68C, 0xF014169D, 0xD198DFEF );
  TEST_RR_OP( 3, pv.add.h, 0x795F026B, 0x7ABB8DD7, 0xFEA47494 );
  TEST_RR_OP( 4, pv.add.h, 0x8ABE2A6C, 0xAA4F3E71, 0xE06FEBFB );
  # pv.add.sc.h
  TEST_RR_OP( 5, pv.add.sc.h, 0x603D0BE0, 0xFC7EA821, 0x94BF63BF );
  TEST_RR_OP( 6, pv.add.sc.h, 0x4A3F89DF, 0x8E28CDC8, 0x3230BC17 );
  TEST_RR_OP( 7, pv.add.sc.h, 0x2034B556, 0x506CE58E, 0x4436CFC8 );
  # pv.add.sci.h
  TEST_SIMM6_OP(  8, pv.add.sci.h, 0x77371C0E, 0x772C1C03, 11 );
  TEST_SIMM6_OP(  9, pv.add.sci.h, 0xD1BA3380, 0xD1AF3375, 11 );
  TEST_SIMM6_OP( 10, pv.add.sci.h, 0x6E73CC2D, 0x6E68CC22, 11 );
  # pv.add.b
  TEST_RR_OP( 11, pv.add.b, 0x8A1518C0, 0x3E50B3BE, 0x4CC56502 );
  TEST_RR_OP( 12, pv.add.b, 0xE8E21596, 0x7ECB21CB, 0x6A17F4CB );
  TEST_RR_OP( 13, pv.add.b, 0xD48653D2, 0x2E741840, 0xA6123B92 );
  # pv.add.sc.b
  TEST_RR_OP( 14, pv.add.sc.b, 0xC96CF4FF, 0x52F57D88, 0x86A5D077 );
  TEST_RR_OP( 15, pv.add.sc.b, 0x877D91A1, 0x2F253949, 0x694FD558 );
  TEST_RR_OP( 16, pv.add.sc.b, 0xC6646B7D, 0x28C6CDDF, 0x1E09659E );
  # pv.add.sci.b
  TEST_SIMM6_OP( 17, pv.add.sci.b, 0x3820508C, 0x2D154581, 11 );
  TEST_SIMM6_OP( 18, pv.add.sci.b, 0xBF98380C, 0xB48D2D01, 11 );
  TEST_SIMM6_OP( 19, pv.add.sci.b, 0x90AAEB98, 0x859FE08D, 11 );

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
