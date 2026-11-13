# See LICENSE for license details.

#*****************************************************************************
# vfmin_h.S
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
  # 0xFFFFFF3E;   // 1.618
  # 0xFFFFFF34;   // 0.250244
  # 0xFFFFFF56;   // 100.123456789

  TEST_RR_OP( 2,  vfmin.b, 0x3E343442, 0x423E3456, 0x3E345642 );
  TEST_RR_OP( 3,  vfmax.b, 0x423E5656, 0x423E3456, 0x3E345642 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
