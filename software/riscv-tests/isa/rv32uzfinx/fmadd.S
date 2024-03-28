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

  TEST_RRR_PLUSD_OP( 2,  fmadd.s, 0x40600000, 0x3F800000, 0x40200000, 0x3F800000 ); #   3.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 3,  fmadd.s, 0x449A8666, 0xBF800000, 0xC49A6333, 0x3F8CCCCD ); #1236.2, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 4,  fmadd.s, 0xC1400000, 0x40000000, 0xC0A00000, 0xC0000000 ); # -12.0,  2.0,    -5.0, -2.0

  TEST_RRR_PLUSD_OP( 5,  fnmadd.s, 0xC0600000, 0x3F800000, 0x40200000, 0x3F800000 ); #   -3.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 6,  fnmadd.s, 0xC49A8666, 0xBF800000, 0xC49A6333, 0x3F8CCCCD ); #-1236.2, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 7,  fnmadd.s, 0x41400000, 0x40000000, 0xC0A00000, 0xC0000000 ); #   12.0,  2.0,    -5.0, -2.0

  TEST_RRR_PLUSD_OP( 8,  fmsub.s, 0x3FC00000, 0x3F800000, 0x40200000, 0x3F800000 ); #   -1.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 9,  fmsub.s, 0x449A4000, 0xBF800000, 0xC49A6333, 0x3F8CCCCD ); # 1234.0, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 10,  fmsub.s, 0xC1000000, 0x40000000, 0xC0A00000, 0xC0000000 ); #   -8.0,  2.0,    -5.0, -2.0

  TEST_RRR_PLUSD_OP( 11,  fnmsub.s, 0xBFC00000, 0x3F800000, 0x40200000, 0x3F800000 ); #   -1.5,  1.0,     2.5,  1.0
  TEST_RRR_PLUSD_OP( 12,  fnmsub.s, 0xC49A4000, 0xBF800000, 0xC49A6333, 0x3F8CCCCD ); #-1234.0, -1.0, -1235.1,  1.1
  TEST_RRR_PLUSD_OP( 13,  fnmsub.s, 0x41000000, 0x40000000, 0xC0A00000, 0xC0000000 ); #    8.0,  2.0,    -5.0, -2.0

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
