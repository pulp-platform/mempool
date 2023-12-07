# See LICENSE for license details.

#*****************************************************************************
# fsgnj.S
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

  TEST_RR_OP( 2,  fsgnj.h, 0xFFFF4100, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 3,  fsgnj.h, 0xFFFF64D3, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP( 4,  fsgnj.h, 0xFFFFBC66, 0xFFFF3C66, 0xFFFFE4D3 );

  TEST_RR_OP( 5,  fsgnjn.h, 0xFFFFC100, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 6,  fsgnjn.h, 0xFFFFE4D3, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP( 7,  fsgnjn.h, 0xFFFF3C66, 0xFFFF3C66, 0xFFFFE4D3 );

  TEST_RR_OP( 8,  fsgnjx.h, 0xFFFF4100, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 9,  fsgnjx.h, 0xFFFFE4D3, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP(10,  fsgnjx.h, 0xFFFFBC66, 0xFFFF3C66, 0xFFFFE4D3 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
