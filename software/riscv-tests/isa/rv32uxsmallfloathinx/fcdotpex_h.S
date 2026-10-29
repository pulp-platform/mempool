# See LICENSE for license details.

#*****************************************************************************
# fcdotpex_h.S
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
  # BC00 -1
  # 4500 5
  # 3C00 1
  # 4300 3.5

  #                                CHECK       RS1         RS2         RD
  TEST_RRR_OP( 2,  fcdotpex.s.h,   0x00004000, 0x3C003C00, 0x3C003C00, 0x00000000 );
  TEST_RRR_OP( 3,  fccdotpex.s.h,  0x00004000, 0x3C003C00, 0x3C00BC00, 0x00000000 );

  TEST_RRR_OP( 4,  fcdotpex.s.h,   0xC1004780, 0x41004500, 0x3C003C00, 0x00000000 );
  TEST_RRR_OP( 5,  fcdotpex.s.h,   0xBE004840, 0x41004500, 0x3C003C00, 0x3C003C00 );
  TEST_RRR_OP( 6,  fcndotpex.s.h,  0x4300C680, 0x41004500, 0x3C003C00, 0x3C003C00 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
