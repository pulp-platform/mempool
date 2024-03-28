# See LICENSE for license details.

#*****************************************************************************
# fsgnj.S
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

  TEST_RR_OP( 2,  fsgnj.s, 0x40200000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 3,  fsgnj.s, 0x449A6333, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP( 4,  fsgnj.s, 0xBF8CCCCD, 0x3F8CCCCD, 0xC49A6333 );

  TEST_RR_OP( 5,  fsgnjn.s, 0xC0200000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 6,  fsgnjn.s, 0xC49A6333, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP( 7,  fsgnjn.s, 0x3F8CCCCD, 0x3F8CCCCD, 0xC49A6333 );

  TEST_RR_OP( 8,  fsgnjx.s, 0x40200000, 0x40200000, 0x3F800000 );
  TEST_RR_OP( 9,  fsgnjx.s, 0xC49A6333, 0xC49A6333, 0x3F8CCCCD );
  TEST_RR_OP(10,  fsgnjx.s, 0xBF8CCCCD, 0x3F8CCCCD, 0xC49A6333 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
