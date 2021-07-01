# See LICENSE for license details.

#*****************************************************************************
# p_beqimm.S
#-----------------------------------------------------------------------------
#
# Test p.beqimm instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Branch tests
  #-------------------------------------------------------------

  # Each test checks both forward and backward branches

  TEST_BRI_OP_TAKEN( 2, p.beqimm,  0,  0 );
  TEST_BRI_OP_TAKEN( 3, p.beqimm,  1,  1 );
  TEST_BRI_OP_TAKEN( 4, p.beqimm, -1, -1 );

  TEST_BRI_OP_NOTTAKEN( 5, p.beqimm,  0,  1 );
  TEST_BRI_OP_NOTTAKEN( 6, p.beqimm,  1,  0 );
  TEST_BRI_OP_NOTTAKEN( 7, p.beqimm, -1,  1 );
  TEST_BRI_OP_NOTTAKEN( 8, p.beqimm,  1, -1 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_BRI_SRC1_BYPASS(  9, 0, p.beqimm, 0, -1 );
  TEST_BRI_SRC1_BYPASS( 10, 1, p.beqimm, 0, -1 );
  TEST_BRI_SRC1_BYPASS( 11, 2, p.beqimm, 0, -1 );

  #-------------------------------------------------------------
  # Test delay slot instructions not executed nor bypassed
  #-------------------------------------------------------------

  TEST_CASE( 12, x1, 3, \
    li  x1, 1; \
    p.beqimm x0, 0, 1f; \
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
