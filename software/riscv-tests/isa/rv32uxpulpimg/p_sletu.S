# See LICENSE for license details.

#*****************************************************************************
# p_sletu.S
#-----------------------------------------------------------------------------
#
# Test p.sletu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.sletu, 1, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.sletu, 1, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.sletu, 0, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.sletu, 1, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.sletu, 0, 0x7a08f69a, 0x584022e8 );
  TEST_RR_OP( 7, p.sletu, 0, 0xf0c13aa0, 0xe6fa0f05 );
  TEST_RR_OP( 8, p.sletu, 1, 0x76442e72, 0x7644c053 );
  TEST_RR_OP( 9, p.sletu, 0, 0x82dc75c0, 0x7a08f69a );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 10, p.sletu, 1,  50, 51 );
  TEST_RR_SRC2_EQ_DEST( 11, p.sletu, 0,  210, 8 );

  TEST_RR_SRC12_EQ_DEST( 12, p.sletu, 1, 5 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 13, 0, p.sletu, 0, 53, 11 );
  TEST_RR_DEST_BYPASS( 14, 1, p.sletu, 1, 11, 72 );
  TEST_RR_DEST_BYPASS( 15, 2, p.sletu, 0, 15, 11 );

  TEST_RR_SRC12_BYPASS( 16, 0, 0, p.sletu, 0, 13, 2 );
  TEST_RR_SRC12_BYPASS( 17, 0, 1, p.sletu, 0, 14, 5 );
  TEST_RR_SRC12_BYPASS( 18, 0, 2, p.sletu, 0, 15, 1 );
  TEST_RR_SRC12_BYPASS( 19, 1, 0, p.sletu, 1, 11, 12 );
  TEST_RR_SRC12_BYPASS( 20, 1, 1, p.sletu, 1, 0, 1 );
  TEST_RR_SRC12_BYPASS( 21, 2, 0, p.sletu, 1, 15, 15 );

  TEST_RR_SRC21_BYPASS( 22, 0, 0, p.sletu, 0, 13,  2 );
  TEST_RR_SRC21_BYPASS( 23, 0, 1, p.sletu, 0, 14,  5 );
  TEST_RR_SRC21_BYPASS( 24, 0, 2, p.sletu, 1, 1,  15 );
  TEST_RR_SRC21_BYPASS( 25, 1, 0, p.sletu, 0, 13, 12 );
  TEST_RR_SRC21_BYPASS( 26, 1, 1, p.sletu, 0, 14,  1 );
  TEST_RR_SRC21_BYPASS( 27, 2, 0, p.sletu, 1, 15, 15 );

  TEST_RR_ZEROSRC1( 28, p.sletu, 1, 15 );
  TEST_RR_ZEROSRC2( 29, p.sletu, 0, 120 );
  TEST_RR_ZEROSRC12( 30, p.sletu, 1 );

  TEST_RR_ZERODEST( 31, p.sletu, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
