# See LICENSE for license details.

#*****************************************************************************
# vfmac_h.S
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

  #                         CHECK       RS1         RS2         RD
  TEST_RRR_OP( 2,  vfmac.b, 0x45564F45, 0x423E3442, 0x3E34563E, 0x34564234 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
