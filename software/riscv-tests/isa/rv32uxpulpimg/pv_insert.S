# See LICENSE for license details.

#*****************************************************************************
# pv_insert.S
#-----------------------------------------------------------------------------
#
# Test pv.insert instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Functional tests
  #-------------------------------------------------------------

  # load immediate in test register necessary before execution
  # of each test case because the output is dependent on the
  # previous state of rD

  # pv.insert.h
  li x14, 0x6ACB7454;
  TEST_UIMM6_OP( 2, pv.insert.h, 0x6ACBF419, 0x3A12F419, 0 );
  li x14, 0x2BCBE5BA;
  TEST_UIMM6_OP( 3, pv.insert.h, 0x2BCB3FEE, 0x86013FEE, 0 );
  li x14, 0x8E18DBE7;
  TEST_UIMM6_OP( 4, pv.insert.h, 0x8E18C59F, 0x7153C59F, 0 );
  li x14, 0x57DF0195;
  TEST_UIMM6_OP( 5, pv.insert.h, 0x00F60195, 0x267700F6, 1 );
  li x14, 0x7825C668;
  TEST_UIMM6_OP( 6, pv.insert.h, 0x17F7C668, 0x04A017F7, 1 );
  li x14, 0xDBC05DC7;
  TEST_UIMM6_OP( 7, pv.insert.h, 0xF7455DC7, 0x3569F745, 1 );
  # pv.insert.b
  li x14, 0x5C93979B;
  TEST_UIMM6_OP( 8, pv.insert.b, 0x5C93979C, 0x955C289C, 0 );
  li x14, 0x4696DE77;
  TEST_UIMM6_OP( 9, pv.insert.b, 0x4696DEB0, 0x00E6ADB0, 0 );
  li x14, 0x48024613;
  TEST_UIMM6_OP( 10, pv.insert.b, 0x4802465E, 0xE580375E, 0 );
  li x14, 0x55963E26;
  TEST_UIMM6_OP( 11, pv.insert.b, 0x5596FC26, 0x215C2AFC, 1 );
  li x14, 0xAA2930B8;
  TEST_UIMM6_OP( 12, pv.insert.b, 0xAA29DCB8, 0xE0318DDC, 1 );
  li x14, 0x844521DE;
  TEST_UIMM6_OP( 13, pv.insert.b, 0x84459DDE, 0x12ED4F9D, 1 );
  li x14, 0xFE27DE9A;
  TEST_UIMM6_OP( 14, pv.insert.b, 0xFED1DE9A, 0xC72B60D1, 2 );
  li x14, 0x41075730;
  TEST_UIMM6_OP( 15, pv.insert.b, 0x41065730, 0x63ED6A06, 2 );
  li x14, 0xFD9C6336;
  TEST_UIMM6_OP( 16, pv.insert.b, 0xFD426336, 0xA924A142, 2 );
  li x14, 0x2A3A8341;
  TEST_UIMM6_OP( 17, pv.insert.b, 0x513A8341, 0x6B50F251, 3 );
  li x14, 0x59FBF2A7;
  TEST_UIMM6_OP( 18, pv.insert.b, 0x31FBF2A7, 0x41767331, 3 );
  li x14, 0xE056E2B2;
  TEST_UIMM6_OP( 19, pv.insert.b, 0x8C56E2B2, 0x2B08038C, 3 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_UIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_UIMM6_DEST_BYPASS, TEST_UIMM6_SRC1_BYPASS,
  # TEST_UIMM6_ZEROSRC1, TEST_UIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
