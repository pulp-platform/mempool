# See LICENSE for license details.

#*****************************************************************************
# vfcpka_h.S
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

  # 0x4048F5C3;   // 3.14
  # 0xC048F5C3;  // -3.14
  # 0x3FCF1AA0;   // 1.618
  # 0xBFCF1AA0;  // -1.618

  # 0xFFFF4248;   // 3.14
  # 0xFFFFC248;  // -3.14
  # 0xFFFF3E79;   // 1.618
  # 0xFFFFBE79;  // -1.618

  TEST_RR_OP( 2,  vfcpka.h.s, 0x3E794248, 0x4048F5C3, 0x3FCF1AA0 );
  TEST_RR_OP( 3,  vfcpka.h.s, 0xBE79C248, 0xC048F5C3, 0xBFCF1AA0 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
