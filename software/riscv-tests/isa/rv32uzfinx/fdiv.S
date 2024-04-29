# See LICENSE for license details.

#*****************************************************************************
# fdiv.S
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

  TEST_RR_OP( 2,  fdiv.s, 0x3F93EEE0, 0x40490FDB, 0x402DF854 );
  TEST_RR_OP( 3,  fdiv.s, 0xBF7FC5A2, 0xC49A4000, 0x449A6333 );
  TEST_RR_OP( 4,  fdiv.s, 0x40490FDB, 0x40490FDB, 0x3F800000 );

  TEST_R_OP( 5,  fsqrt.s, 0x3FE2DFC5, 0x40490FDB );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
