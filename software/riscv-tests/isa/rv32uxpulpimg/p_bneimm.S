# See LICENSE for license details.

#*****************************************************************************
# p_bneimm.S
#-----------------------------------------------------------------------------
#
# Test p.bneimm instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Branch tests
  #-------------------------------------------------------------

  # Each test checks both forward and backward branches

  TEST_BRI_OP_TAKEN( 2, p.bneimm,  0,  1 );
  TEST_BRI_OP_TAKEN( 3, p.bneimm,  1,  0 );
  TEST_BRI_OP_TAKEN( 4, p.bneimm, -1,  1 );
  TEST_BRI_OP_TAKEN( 5, p.bneimm,  1, -1 );

  TEST_BRI_OP_NOTTAKEN( 6, p.bneimm,  0,  0 );
  TEST_BRI_OP_NOTTAKEN( 7, p.bneimm,  1,  1 );
  TEST_BRI_OP_NOTTAKEN( 8, p.bneimm, -1, -1 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_BRI_SRC1_BYPASS(  9, 0, p.bneimm, 0, 0 );
  TEST_BRI_SRC1_BYPASS( 10, 1, p.bneimm, 0, 0 );
  TEST_BRI_SRC1_BYPASS( 11, 2, p.bneimm, 0, 0 );

  #-------------------------------------------------------------
  # Test delay slot instructions not executed nor bypassed
  #-------------------------------------------------------------

  TEST_CASE( 12, x1, 3, \
    li  x1, 1; \
    p.bneimm x1, 0, 1f; \
    addi x1, x1, 1; \
    addi x1, x1, 1; \
    addi x1, x1, 1; \
    addi x1, x1, 1; \
1:  addi x1, x1, 1; \
    addi x1, x1, 1; \
  )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
