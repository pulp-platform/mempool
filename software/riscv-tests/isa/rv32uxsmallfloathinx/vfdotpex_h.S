# See LICENSE for license details.

#*****************************************************************************
# vfdotpex_h.S
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
  # 3C00 1

  #                               CHECK       RS1         RS2         RD
  TEST_RRR_OP( 2,  vfdotpex.s.h,  0xC49A1000, 0x3C003C00, 0x4100E4D3, 0x00000000 );
  TEST_RRR_OP( 3,  vfdotpex.s.h,  0xC50B8800, 0x3C003C00, 0x4100E4D3, 0xC47A0000 );
  TEST_RRR_OP( 4,  vfndotpex.s.h, 0x43688000, 0x3C003C00, 0x4100E4D3, 0xC47A0000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
