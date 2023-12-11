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

  # 4100 2.5
  # E4D3 -1235
  # BC00 -1
  # 3C00 1
  # 64D4 1236
  # 4300 3.5

  #                         CHECK       RS1         RS2         RD
  TEST_RRR_OP( 2,  vfmac.h, 0x4100E4D3, 0x00000000, 0x3C003C00, 0x4100E4D3 );
  TEST_RRR_OP( 3,  vfmac.h, 0xC60064D5, 0xC0003C00, 0x430064D4, 0x3C003C00 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
