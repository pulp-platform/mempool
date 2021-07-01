# See LICENSE for license details.

#*****************************************************************************
# p_abs.S
#-----------------------------------------------------------------------------
#
# Test p.abs instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_R_OP( 2, p.abs, 0x00000000, 0x00000000 );
  TEST_R_OP( 3, p.abs, 0x00000001, 0xffffffff );

  TEST_R_OP( 4, p.abs, 0x12577823, 0x12577823 );
  TEST_R_OP( 5, p.abs, 0x7a89cdbb, 0x85763245 );
  TEST_R_OP( 6, p.abs, 0x69879573, 0x69879573 );
  TEST_R_OP( 7, p.abs, 0x67cb67cc, 0x98349834 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_R_SRC1_EQ_DEST( 8, p.abs, 25, -25 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_R_DEST_BYPASS( 9,  0, p.abs, 102, 102 )
  TEST_R_DEST_BYPASS( 10, 1, p.abs, 500, -500 )
  TEST_R_DEST_BYPASS( 11, 2, p.abs, 21,  21 )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
