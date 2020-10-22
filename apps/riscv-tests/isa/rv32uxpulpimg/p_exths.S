# See LICENSE for license details.

#*****************************************************************************
# p_exths.S
#-----------------------------------------------------------------------------
#
# Test p.exths instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_R_OP( 2, p.exths, 0x00000000, 0x00000000 );
  TEST_R_OP( 3, p.exths, 0xffffffff, 0xffffffff );

  TEST_R_OP( 4, p.exths, 0x00000000, 0xffff0000 );
  TEST_R_OP( 5, p.exths, 0xffffffff, 0x0000ffff );

  TEST_R_OP( 6, p.exths, 0xFFFF9549, 0xA8E29549 );
  TEST_R_OP( 7, p.exths, 0x00003051, 0xC2913051 );
  TEST_R_OP( 8, p.exths, 0xFFFFDD5C, 0xA10CDD5C );
  TEST_R_OP( 9, p.exths, 0x00003277, 0x7E9B3277 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_R_SRC1_EQ_DEST( 10, p.exths, 0xFFFFA2D2, 0x14EEA2D2 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_R_DEST_BYPASS( 11, 0, p.exths, 0xFFFF88D0, 0x2D0D88D0 )
  TEST_R_DEST_BYPASS( 12, 1, p.exths, 0x00003550, 0xDD7F3550 )
  TEST_R_DEST_BYPASS( 13, 2, p.exths, 0xFFFF8E5F, 0x801E8E5F )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
