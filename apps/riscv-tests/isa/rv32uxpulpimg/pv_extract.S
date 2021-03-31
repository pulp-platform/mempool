# See LICENSE for license details.

#*****************************************************************************
# pv_extract.S
#-----------------------------------------------------------------------------
#
# Test pv.extract instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Functional tests
  #-------------------------------------------------------------

  # pv.extract.h
  TEST_SIMM6_OP( 2, pv.extract.h, 0x00000DEA, 0x53F90DEA, 0 );
  TEST_SIMM6_OP( 3, pv.extract.h, 0x00000315, 0xC6990315, 0 );
  TEST_SIMM6_OP( 4, pv.extract.h, 0x00005B08, 0xE1415B08, 0 );
  TEST_SIMM6_OP( 5, pv.extract.h, 0x00003654, 0x3654249D, 1 );
  TEST_SIMM6_OP( 6, pv.extract.h, 0x00002EE3, 0x2EE3D9FE, 1 );
  TEST_SIMM6_OP( 7, pv.extract.h, 0xFFFF93B1, 0x93B1AA99, 1 );
  # pv.extract.b
  TEST_SIMM6_OP( 8, pv.extract.b, 0xFFFFFFD9, 0x53C073D9, 0 );
  TEST_SIMM6_OP( 9, pv.extract.b, 0x0000001F, 0x269EFC1F, 0 );
  TEST_SIMM6_OP( 10, pv.extract.b, 0xFFFFFFAB, 0x0E8CD3AB, 0 );
  TEST_SIMM6_OP( 11, pv.extract.b, 0x0000004A, 0xF7964A55, 1 );
  TEST_SIMM6_OP( 12, pv.extract.b, 0x0000006C, 0x1F366C84, 1 );
  TEST_SIMM6_OP( 13, pv.extract.b, 0x0000005B, 0x11205B09, 1 );
  TEST_SIMM6_OP( 14, pv.extract.b, 0x00000036, 0x2C36C818, 2 );
  TEST_SIMM6_OP( 15, pv.extract.b, 0x00000003, 0x4C039923, 2 );
  TEST_SIMM6_OP( 16, pv.extract.b, 0x0000007E, 0x057ED2EE, 2 );
  TEST_SIMM6_OP( 17, pv.extract.b, 0x00000056, 0x56B005BB, 3 );
  TEST_SIMM6_OP( 18, pv.extract.b, 0xFFFFFFE7, 0xE7798BAA, 3 );
  TEST_SIMM6_OP( 19, pv.extract.b, 0xFFFFFFF3, 0xF3F956A2, 3 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_SIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_SIMM6_DEST_BYPASS, TEST_SIMM6_SRC1_BYPASS,
  # TEST_SIMM6_ZEROSRC1, TEST_SIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
