# See LICENSE for license details.

#*****************************************************************************
# p_extbs.S
#-----------------------------------------------------------------------------
#
# Test p.extbs instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_R_OP( 2, p.extbs, 0x00000000, 0x00000000 );
  TEST_R_OP( 3, p.extbs, 0xffffffff, 0xffffffff );

  TEST_R_OP( 4, p.extbs, 0x00000000, 0xffffff00 );
  TEST_R_OP( 5, p.extbs, 0xffffffff, 0x000000ff );

  TEST_R_OP( 6, p.extbs, 0x00000027, 0x2E16B927 );
  TEST_R_OP( 7, p.extbs, 0xFFFFFF9A, 0x0CB2439A );
  TEST_R_OP( 8, p.extbs, 0x00000009, 0x9CA4EE09 );
  TEST_R_OP( 9, p.extbs, 0x00000034, 0xDD8C3E34 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_R_SRC1_EQ_DEST( 10, p.extbs, 0xFFFFFF92, 0xE9E9D692 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_R_DEST_BYPASS( 11, 0, p.extbs, 0x00000067, 0x4C740267 )
  TEST_R_DEST_BYPASS( 12, 1, p.extbs, 0xFFFFFFBD, 0xDB4D5EBD )
  TEST_R_DEST_BYPASS( 13, 2, p.extbs, 0x00000018, 0xB5C96F18 )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
