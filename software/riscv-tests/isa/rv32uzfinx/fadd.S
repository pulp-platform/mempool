# See LICENSE for license details.

#*****************************************************************************
# fadd.S
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

  TEST_RR_OP( 2,  fadd.s, 0x40600000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 3,  fadd.s, 0xC49A4000, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP( 4,  fadd.s, 0x40490FDB, 0x40490FDB, 0x322BCC77 );

  TEST_RR_OP( 5,  fsub.s, 0x3FC00000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 6,  fsub.s, 0xC49A4000, 0xC49A6333, 0xBF8CCCCD );
  TEST_RR_OP( 7,  fsub.s, 0x40490FDB, 0x40490FDB, 0x322BCC77 );

  TEST_RR_OP( 8,  fmul.s, 0x40200000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 9,  fmul.s, 0x44A9D385, 0xC49A6333, 0xBF8CCCCD );
  TEST_RR_OP(10,  fmul.s, 0x3306EE2D, 0x40490FDB, 0x322BCC77 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
