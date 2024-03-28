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

  TEST_RR_OP( 2,  vfadd.h, 0xE4D24300, 0xE4D34100, 0x3C663C00 );
  TEST_RR_OP( 3,  vfadd.h, 0x4248E4D2, 0x4248E4D3, 0x00003C66 );

  TEST_RR_OP( 4,  vfsub.h, 0xE4D23E00, 0xE4D34100, 0xBC663C00 );
  TEST_RR_OP( 5,  vfsub.h, 0x4248E4D2, 0x4248E4D3, 0x0000BC66 );

  TEST_RR_OP( 6,  vfmul.h, 0x654E4100, 0xE4D34100, 0xBC663C00 );
  TEST_RR_OP( 7,  vfmul.h, 0x0000654E, 0x4248E4D3, 0x0000BC66 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
