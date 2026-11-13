# See LICENSE for license details.

#*****************************************************************************
# vfcpka_h.S
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

  TEST_RR_OP( 2,  vfcpkb.b.s, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3,  vfcpka.b.s, 0x00003E42, 0x4048F5C3, 0x3FCF1AA0 );
  #TEST_RR_OP( 4,  vfcpkb.b.s, 0x3E420000, 0x4048F5C3, 0x3FCF1AA0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
