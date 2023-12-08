# See LICENSE for license details.

#*****************************************************************************
# fmin_b.S
#-----------------------------------------------------------------------------
#
# Test add instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # 0xFFFFFF42;   // 3.14
  # 0xFFFFFF56;   // 100.123456789
  # 0xFFFFFFD6;   // -100.123456789

  TEST_RR_OP( 2,  fmin.b, 0xFFFFFF42, 0xFFFFFF56, 0xFFFFFF42 );
  TEST_RR_OP( 3,  fmin.b, 0xFFFFFFD6, 0xFFFFFFD6, 0xFFFFFF42 );

  TEST_RR_OP( 8,  fmax.b, 0xFFFFFF56, 0xFFFFFF56, 0xFFFFFF42 );
  TEST_RR_OP( 9,  fmax.b, 0xFFFFFF42, 0xFFFFFFD6, 0xFFFFFF42 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
