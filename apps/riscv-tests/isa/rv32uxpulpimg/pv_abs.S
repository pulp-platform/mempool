# See LICENSE for license details.

#*****************************************************************************
# pv_abs.S
#-----------------------------------------------------------------------------
#
# Test pv.abs instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.abs.h
  TEST_R_OP( 2, pv.abs.h, 0x10081554, 0xEFF8EAAC );
  TEST_R_OP( 3, pv.abs.h, 0x369800DA, 0x3698FF26 );
  TEST_R_OP( 4, pv.abs.h, 0x7C127B74, 0x7C12848C );
  # pv.abs.b
  TEST_R_OP( 5, pv.abs.b, 0x3A444335, 0x3ABC4335 );
  TEST_R_OP( 6, pv.abs.b, 0x2B743B7C, 0x2B8C3B7C );
  TEST_R_OP( 7, pv.abs.b, 0x70362066, 0x70362066 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_R_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # TEST_R_DEST_BYPASS

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
