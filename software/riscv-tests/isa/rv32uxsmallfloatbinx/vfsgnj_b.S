# See LICENSE for license details.

#*****************************************************************************
# vfsgnj_h.S
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

  #0xFFFFFF42;   // 3.14
  #0xFFFFFFC2;   // -3.14
  #0xFFFFFF3E;   // 1.618
  #0xFFFFFFBE;   // -1.618
  #0xFFFFFF41;   // 2.39062
  #0xFFFFFFC1;   // -2.39062
  #0xFFFFFF34;   // 0.250244
  #0xFFFFFFB4;   // -0.250244

  TEST_RR_OP( 2,  vfsgnj.b, 0xC2BEC1B4, 0x423E4134, 0xC2BEC1B4 );
  TEST_RR_OP( 3,  vfsgnjn.b, 0x423E4134, 0x423E4134, 0xC2BEC1B4 );
  TEST_RR_OP( 4,  vfsgnjx.b, 0xC2BEC1B4, 0x423E4134, 0xC2BEC1B4 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
