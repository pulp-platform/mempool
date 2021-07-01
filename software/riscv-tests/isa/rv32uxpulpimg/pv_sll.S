# See LICENSE for license details.

#*****************************************************************************
# pv_sll.S
#-----------------------------------------------------------------------------
#
# Test pv.sll instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.sll.h
  TEST_RR_OP( 2, pv.sll.h, 0x40000E80, 0xCC85D0E8, 0x000E0004 );
  TEST_RR_OP( 3, pv.sll.h, 0xF0802C00, 0x83E1502C, 0x00070008 );
  TEST_RR_OP( 4, pv.sll.h, 0x20005470, 0x8AA1551C, 0x000D0002 );
  # pv.sll.sc.h
  TEST_RR_OP( 5, pv.sll.sc.h, 0x81F03608, 0x103E26C1, 0x000A0003 );
  TEST_RR_OP( 6, pv.sll.sc.h, 0x1B800F00, 0x0437CE1E, 0x00080007 );
  TEST_RR_OP( 7, pv.sll.sc.h, 0xC7002900, 0xE5C75029, 0x000D0008 );
  # pv.sll.sci.h
  TEST_UIMM6_OP(  8, pv.sll.sci.h, 0x46002600, 0x48233B93, 9 );
  TEST_UIMM6_OP(  9, pv.sll.sci.h, 0x9600AC00, 0x344B9356, 9 );
  TEST_UIMM6_OP( 10, pv.sll.sci.h, 0x40002E00, 0xB2A0E417, 9 );
  # pv.sll.b
  TEST_RR_OP( 11, pv.sll.b, 0x7EE05CA8, 0x3FCE5C2A, 0x01040002 );
  TEST_RR_OP( 12, pv.sll.b, 0xA45E8034, 0xE95E5934, 0x02000700 );
  TEST_RR_OP( 13, pv.sll.b, 0xB0780068, 0xFB8FA8B4, 0x04030501 );
  # pv.sll.sc.b
  TEST_RR_OP( 14, pv.sll.sc.b, 0xF05000C0, 0x5FF510FC, 0x02020004 );
  TEST_RR_OP( 15, pv.sll.sc.b, 0xA0C0B0A0, 0x2A6CFB1A, 0x01000604 );
  TEST_RR_OP( 16, pv.sll.sc.b, 0x047E94F8, 0x823FCAFC, 0x07010601 );
  # pv.sll.sci.b
  TEST_UIMM6_OP( 17, pv.sll.sci.b, 0x60002020, 0x8BA0A901, 5 );
  TEST_UIMM6_OP( 18, pv.sll.sci.b, 0x604020E0, 0x83CAE947, 5 );
  TEST_UIMM6_OP( 19, pv.sll.sci.b, 0x0020A060, 0x98F185C3, 5 );

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
