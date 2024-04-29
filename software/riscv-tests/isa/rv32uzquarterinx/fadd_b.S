# See LICENSE for license details.

#*****************************************************************************
# fadd_b.S
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
  # 0xFFFFFF3E;   // 1.618
  # 0xFFFFFF34;   // 0.250244
  # 0xFFFFFF56;   // 100.123456789

  TEST_RR_OP( 2,  fadd.b, 0xFFFFFF44, 0xFFFFFF42, 0xFFFFFF3E );
  TEST_RR_OP( 3,  fadd.b, 0xFFFFFF3F, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RR_OP( 4,  fadd.b, 0xFFFFFF56, 0xFFFFFF34, 0xFFFFFF56 );

  TEST_RR_OP( 5,  fsub.b, 0xFFFFFF3E, 0xFFFFFF42, 0xFFFFFF3E );
  TEST_RR_OP( 6,  fsub.b, 0xFFFFFF3D, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RR_OP( 7,  fsub.b, 0xFFFFFFD6, 0xFFFFFF34, 0xFFFFFF56 );

  TEST_RR_OP( 8,  fmul.b, 0xFFFFFF44, 0xFFFFFF42, 0xFFFFFF3E );
  TEST_RR_OP( 9,  fmul.b, 0xFFFFFF36, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RR_OP(10,  fmul.b, 0xFFFFFF4E, 0xFFFFFF34, 0xFFFFFF56 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
