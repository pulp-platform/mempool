# See LICENSE for license details.

#*****************************************************************************
# fmin.S
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

  TEST_RR_OP( 2,  fmin.h, 0xFFFF3C00, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 3,  fmin.h, 0xFFFFE4D3, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP( 4,  fmin.h, 0xFFFFE4D3, 0xFFFF3C66, 0xFFFFE4D3 );
  TEST_RR_OP( 5,  fmin.h, 0xFFFFE4D3, 0xFFFF7E00, 0xFFFFE4D3 );
  TEST_RR_OP( 6,  fmin.h, 0xFFFF0000, 0xFFFF4248, 0xFFFF0000 );
  TEST_RR_OP( 7,  fmin.h, 0xFFFFC000, 0xFFFFBC00, 0xFFFFC000 );

  TEST_RR_OP( 8,  fmax.h, 0xFFFF4100, 0xFFFF4100, 0xFFFF3C00 );
  TEST_RR_OP( 9,  fmax.h, 0xFFFF3C66, 0xFFFFE4D3, 0xFFFF3C66 );
  TEST_RR_OP(10,  fmax.h, 0xFFFF3C66, 0xFFFF3C66, 0xFFFFE4D3 );
  TEST_RR_OP(11,  fmax.h, 0xFFFFE4D3, 0xFFFF7E00, 0xFFFFE4D3 );
  TEST_RR_OP(12,  fmax.h, 0xFFFF4248, 0xFFFF4248, 0xFFFF0000 );
  TEST_RR_OP(13,  fmax.h, 0xFFFFBC00, 0xFFFFBC00, 0xFFFFC000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
