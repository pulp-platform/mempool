# See LICENSE for license details.

#*****************************************************************************
# fmin.S
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

  TEST_RR_OP( 2,  fmin.s, 0x3F800000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 3,  fmin.s, 0xC49A6333, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP( 4,  fmin.s, 0xC49A6333, 0x3F8CCCCD, 0xC49A6333 );
  TEST_RR_OP( 5,  fmin.s, 0xC49A6333, 0x7FC00000, 0xC49A6333 );
  TEST_RR_OP( 6,  fmin.s, 0x322BCC77, 0x40490FDB, 0x322BCC77 );
  TEST_RR_OP( 7,  fmin.s, 0xC0000000, 0xBF800000, 0xC0000000 );

  TEST_RR_OP( 8,  fmax.s, 0x40200000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 9,  fmax.s, 0x3F8CCCCD, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP(10,  fmax.s, 0x3F8CCCCD, 0x3F8CCCCD, 0xC49A6333 );
  TEST_RR_OP(11,  fmax.s, 0xC49A6333, 0x7FC00000, 0xC49A6333 );
  TEST_RR_OP(12,  fmax.s, 0x40490FDB, 0x40490FDB, 0x322BCC77 );
  TEST_RR_OP(13,  fmax.s, 0xBF800000, 0xBF800000, 0xC0000000 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
