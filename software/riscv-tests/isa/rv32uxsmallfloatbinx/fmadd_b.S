# See LICENSE for license details.

#*****************************************************************************
# fmadd_b.S
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

  TEST_RRR_PLUSD_OP( 2,  fmadd.b, 0xFFFFFF45, 0xFFFFFF42, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RRR_PLUSD_OP( 3,  fmadd.b, 0xFFFFFF56, 0xFFFFFF3E, 0xFFFFFF34, 0xFFFFFF56 );
  TEST_RRR_PLUSD_OP( 4,  fmadd.b, 0xFFFFFF4F, 0xFFFFFF34, 0xFFFFFF56, 0xFFFFFF42);

  #TEST_RRR_PLUSD_OP( 5,  fnmadd.b, 0xFFFFFFC5, 0xFFFFFF42, 0xFFFFFF3E, 0xFFFFFF34 );
  #TEST_RRR_PLUSD_OP( 6,  fnmadd.b, 0xFFFFFFD6, 0xFFFFFF3E, 0xFFFFFF34, 0xFFFFFF56 );
  #TEST_RRR_PLUSD_OP( 7,  fnmadd.b, 0xFFFFFFCF, 0xFFFFFF34, 0xFFFFFF56, 0xFFFFFF42 );

  TEST_RRR_PLUSD_OP( 8,  fmsub.b, 0xFFFFFF44, 0xFFFFFF42, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RRR_PLUSD_OP( 9,  fmsub.b, 0xFFFFFFD6, 0xFFFFFF3E, 0xFFFFFF34, 0xFFFFFF56);
  TEST_RRR_PLUSD_OP(10,  fmsub.b, 0xFFFFFF4D, 0xFFFFFF34, 0xFFFFFF56, 0xFFFFFF42);

  TEST_RRR_PLUSD_OP(11,  fnmsub.b, 0xFFFFFFC4, 0xFFFFFF42, 0xFFFFFF3E, 0xFFFFFF34 );
  TEST_RRR_PLUSD_OP(12,  fnmsub.b, 0xFFFFFF56, 0xFFFFFF3E, 0xFFFFFF34, 0xFFFFFF56 );
  TEST_RRR_PLUSD_OP(13,  fnmsub.b, 0xFFFFFFCD, 0xFFFFFF34, 0xFFFFFF56, 0xFFFFFF42 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
