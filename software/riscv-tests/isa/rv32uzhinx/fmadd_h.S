# See LICENSE for license details.

#*****************************************************************************
# fmadd.S
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

  TEST_RRR_PLUSD_OP( 2,  fmadd.h, 0xFFFF4300, 0xFFFF3C00, 0xFFFF4100, 0xFFFF3C00 ); #   3.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 3,  fmadd.h, 0xFFFF64D4, 0xFFFFBC00, 0xFFFFE4D3, 0xFFFF3C66 ); #1236.2, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 4,  fmadd.h, 0xFFFFCA00, 0xFFFF4000, 0xFFFFC500, 0xFFFFC000 ); # -12.0,  2.0,    -5.0, -2.0

  TEST_RRR_PLUSD_OP( 5,  fnmadd.h, 0xFFFFC300, 0xFFFF3C00, 0xFFFF4100, 0xFFFF3C00 ); #   -3.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 6,  fnmadd.h, 0xFFFFE4D4, 0xFFFFBC00, 0xFFFFE4D3, 0xFFFF3C66 ); #-1236.2, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 7,  fnmadd.h, 0xFFFF4A00, 0xFFFF4000, 0xFFFFC500, 0xFFFFC000 ); #   12.0,  2.0,    -5.0, -2.0

  #TEST_RRR_PLUSD_OP( 8,  fmsub.h, 0xFFFFBE00, 0xFFFF3C00, 0xFFFF4100, 0xFFFF3C00 ); #   -1.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 9,  fmsub.h, 0xFFFF64D2, 0xFFFFBC00, 0xFFFFE4D3, 0xFFFF3C66 ); # 1234.0, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP(10,  fmsub.h, 0xFFFFC800, 0xFFFF4000, 0xFFFFC500, 0xFFFFC000 ); #   -8.0,  2.0,    -5.0, -2.0

  TEST_RRR_PLUSD_OP(11,  fnmsub.h, 0xFFFFBE00, 0xFFFF3C00, 0xFFFF4100, 0xFFFF3C00 ); #   -1.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP(12,  fnmsub.h, 0xFFFFE4D2, 0xFFFFBC00, 0xFFFFE4D3, 0xFFFF3C66 ); #-1234.0, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP(13,  fnmsub.h, 0xFFFF4800, 0xFFFF4000, 0xFFFFC500, 0xFFFFC000 ); #    8.0,  2.0,    -5.0, -2.0

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
