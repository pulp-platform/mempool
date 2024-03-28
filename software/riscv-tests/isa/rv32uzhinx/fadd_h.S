# See LICENSE for license details.

#*****************************************************************************
# fadd.S
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

  TEST_RR_OP( 2,  fadd.h, 0xFFFF4300, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 3,  fadd.h, 0xFFFFE4D2, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP( 4,  fadd.h, 0xFFFF4248, 0xFFFF4248, 0xFFFF0000 );

  TEST_RR_OP( 5,  fsub.h, 0xFFFF3E00, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 6,  fsub.h, 0xFFFFE4D2, 0xFFFFE4D3, 0xFFFFBC66 );
  TEST_RR_OP( 7,  fsub.h, 0xFFFF4248, 0xFFFF4248, 0xFFFF0000 );

  TEST_RR_OP( 8,  fmul.h, 0xFFFF4100, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 9,  fmul.h, 0xFFFF654E, 0xFFFFE4D3, 0xFFFFBC66 );
  TEST_RR_OP(10,  fmul.h, 0xFFFF0000, 0xFFFF4248, 0xFFFF0000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
