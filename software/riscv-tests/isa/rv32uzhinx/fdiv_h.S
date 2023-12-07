# See LICENSE for license details.

#*****************************************************************************
# fdiv.S
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

  #TEST_RR_OP( 2,  fdiv.h, 0xFFFF3C9F, 0xFFFF4248, 0xFFFF416F );
  TEST_RR_OP( 3,  fdiv.h, 0xFFFFBBFE, 0xFFFFE4D2, 0xFFFF64D3 );
  TEST_RR_OP( 4,  fdiv.h, 0xFFFF4248, 0xFFFF4248, 0xFFFF3C00 );

  TEST_R_OP( 5,  fsqrt.h, 0xFFFF4700, 0xFFFF5220 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
