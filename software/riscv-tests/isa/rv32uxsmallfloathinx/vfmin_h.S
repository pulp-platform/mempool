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

  TEST_RR_OP( 2,  vfmin.h, 0x3C00E4D3, 0x4100E4D3, 0x3C003C66 );
  TEST_RR_OP( 3,  vfmin.h, 0xE4D3E4D3, 0x3C667E00, 0xE4D3E4D3 );
  TEST_RR_OP( 4,  vfmin.h, 0x0000C000, 0x4248BC00, 0x0000C000 );

  TEST_RR_OP( 5,  vfmax.h, 0x41003C66, 0x4100E4D3, 0x3C003C66 );
  TEST_RR_OP( 6,  vfmax.h, 0x3C66E4D3, 0x3C667E00, 0xE4D3E4D3 );
  TEST_RR_OP( 7,  vfmax.h, 0x4248BC00, 0x4248BC00, 0x0000C000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
