# See LICENSE for license details.

#*****************************************************************************
# vfdotpex_b.S
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


  # 0xFFFFFF42;   // 3.14
  # 0xFFFFFF3C;   // 1
  # 0xFFFFFFBC;   // -1

  #                               CHECK       RS1         RS2         RD
  TEST_RRR_OP( 2,  vfdotpex.h.b,  0x00000000, 0x00004242, 0x0000BC3C, 0x00000000 );
  TEST_RRR_OP( 3,  vfdotpex.h.b,  0x0000C600, 0x00004242, 0x0000BCBC, 0x00000000 );
  TEST_RRR_OP( 4,  vfdotpex.h.b,  0x0000C500, 0x00004242, 0x0000BCBC, 0x00003C00 );
  TEST_RRR_OP( 5,  vfndotpex.h.b, 0x00004700, 0x00004242, 0x0000BCBC, 0x00003C00 );

  TEST_RRR_OP( 6,  vfdotpexa.s.b, 0x00000000, 0x00004242, 0x0000BC3C, 0x00000000 );
  TEST_RRR_OP( 7,  vfdotpexa.s.b, 0xC0C00000, 0x00004242, 0x0000BCBC, 0x00000000 );
  TEST_RRR_OP( 8,  vfdotpexa.s.b, 0xC0A00000, 0x00004242, 0x0000BCBC, 0x3F800000 );
  TEST_RRR_OP( 9,  vfdotpexb.s.b, 0xC0A00000, 0x42420000, 0xBCBC0000, 0x3F800000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
