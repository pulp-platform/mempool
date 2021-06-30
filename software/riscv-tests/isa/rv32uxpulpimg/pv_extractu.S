# See LICENSE for license details.

#*****************************************************************************
# pv_extractu.S
#-----------------------------------------------------------------------------
#
# Test pv.extractu instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Functional tests
  #-------------------------------------------------------------

  # pv.extractu.h
  TEST_UIMM6_OP( 2, pv.extractu.h, 0x0000A18D, 0xED2CA18D, 0 );
  TEST_UIMM6_OP( 3, pv.extractu.h, 0x00006A18, 0x3C576A18, 0 );
  TEST_UIMM6_OP( 4, pv.extractu.h, 0x000040A2, 0x1DAB40A2, 0 );
  TEST_UIMM6_OP( 5, pv.extractu.h, 0x0000BC96, 0xBC969BEC, 1 );
  TEST_UIMM6_OP( 6, pv.extractu.h, 0x0000DF7E, 0xDF7E4D2B, 1 );
  TEST_UIMM6_OP( 7, pv.extractu.h, 0x000099AE, 0x99AEE13C, 1 );
  # pv.extractu.b
  TEST_UIMM6_OP( 8, pv.extractu.b, 0x00000046, 0x8FA19B46, 0 );
  TEST_UIMM6_OP( 9, pv.extractu.b, 0x0000009A, 0xE19C009A, 0 );
  TEST_UIMM6_OP( 10, pv.extractu.b, 0x0000002A, 0x408D722A, 0 );
  TEST_UIMM6_OP( 11, pv.extractu.b, 0x0000006C, 0xA2AF6C67, 1 );
  TEST_UIMM6_OP( 12, pv.extractu.b, 0x0000001F, 0xDE671F25, 1 );
  TEST_UIMM6_OP( 13, pv.extractu.b, 0x00000046, 0x325D46CE, 1 );
  TEST_UIMM6_OP( 14, pv.extractu.b, 0x00000003, 0x4603F967, 2 );
  TEST_UIMM6_OP( 15, pv.extractu.b, 0x000000C1, 0xDBC1292F, 2 );
  TEST_UIMM6_OP( 16, pv.extractu.b, 0x000000D6, 0xE7D631CF, 2 );
  TEST_UIMM6_OP( 17, pv.extractu.b, 0x00000020, 0x20B64275, 3 );
  TEST_UIMM6_OP( 18, pv.extractu.b, 0x000000D6, 0xD64B2CC0, 3 );
  TEST_UIMM6_OP( 19, pv.extractu.b, 0x00000084, 0x845485BD, 3 );

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
