# See LICENSE for license details.

#*****************************************************************************
# vfadd_h.S
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

  TEST_RR_OP( 2,  vfadd.b, 0x443F5644, 0x423E3442, 0x3E34563E );
  TEST_RR_OP( 3,  vfsub.b, 0x3E3DD63E, 0x423E3442, 0x3E34563E );
  TEST_RR_OP( 4,  vfmul.b, 0x44364E44, 0x423E3442, 0x3E34563E );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
