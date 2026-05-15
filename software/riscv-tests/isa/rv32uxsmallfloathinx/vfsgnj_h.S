# See LICENSE for license details.

#*****************************************************************************
# vfsgnj_h.S
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

  TEST_RR_OP( 2,  vfsgnj.h, 0x410064D3, 0x4100E4D3, 0x3C003C66 );
  TEST_RR_OP( 3,  vfsgnj.h, 0x64D3BC66, 0xE4D33C66, 0x3C66E4D3 );

  TEST_RR_OP( 5,  vfsgnjn.h, 0xC100E4D3, 0x4100E4D3, 0x3C003C66 );
  TEST_RR_OP( 6,  vfsgnjn.h, 0xE4D33C66, 0xE4D33C66, 0x3C66E4D3 );

  TEST_RR_OP( 8,  vfsgnjx.h, 0x4100E4D3, 0x4100E4D3, 0x3C003C66 );
  TEST_RR_OP( 9,  vfsgnjx.h, 0xE4D3BC66, 0xE4D33C66, 0x3C66E4D3 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
