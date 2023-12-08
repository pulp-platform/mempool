# See LICENSE for license details.

#*****************************************************************************
# fsgnj_b.S
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
  # 0xFFFFFFC2;   // -3.14
  # 0xFFFFFF3E;   // 1.618
  # 0xFFFFFFBE;   // -1.618

  TEST_RR_OP( 2,  fsgnj.b, 0xFFFFFFC2, 0xFFFFFF42, 0xFFFFFFC2 ); #3.14 -3.14
  TEST_RR_OP( 3,  fsgnj.b, 0xFFFFFF3E, 0xFFFFFF3E, 0xFFFFFF42 ); #1.618 3.14
  TEST_RR_OP( 4,  fsgnj.b, 0xFFFFFFBE, 0xFFFFFFBE, 0xFFFFFFC2 ); #-1.618 -3.14

  TEST_RR_OP( 5,  fsgnjn.b, 0xFFFFFF42, 0xFFFFFF42, 0xFFFFFFC2 );
  TEST_RR_OP( 6,  fsgnjn.b, 0xFFFFFFBE, 0xFFFFFF3E, 0xFFFFFF42 );
  TEST_RR_OP( 7,  fsgnjn.b, 0xFFFFFF3E, 0xFFFFFFBE, 0xFFFFFFC2 );

  TEST_RR_OP( 8,  fsgnjx.b, 0xFFFFFFC2, 0xFFFFFF42, 0xFFFFFFC2 );
  TEST_RR_OP( 9,  fsgnjx.b, 0xFFFFFF3E, 0xFFFFFF3E, 0xFFFFFF42 );
  TEST_RR_OP(10,  fsgnjx.b, 0xFFFFFF3E, 0xFFFFFFBE, 0xFFFFFFC2 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
