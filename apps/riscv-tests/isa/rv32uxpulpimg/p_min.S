# See LICENSE for license details.

#*****************************************************************************
# p_min.S
#-----------------------------------------------------------------------------
#
# Test p.min instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.min, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.min, 0xffffffff, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.min, 0xffffffff, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.min, 0xffffffff, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.min, 0x584022e8, 0x7a08f69a, 0x584022e8 ); # positive-positive, min is rs1
  TEST_RR_OP( 7, p.min, 0x6479b278, 0x76b39000, 0x6479b278 ); # positive-positive, min is rs2
  TEST_RR_OP( 9, p.min, 0x8a7e00c8, 0x8a7e00c8, 0xb4635cea ); # negative-negative, min is rs1
  TEST_RR_OP( 8, p.min, 0xe6fa0f05, 0xf0c13aa0, 0xe6fa0f05 ); # negative-negative, min is rs2

  TEST_RR_OP( 10, p.min, 0xa2d42e72, 0x7644c053, 0xa2d42e72 ); # positive-negative
  TEST_RR_OP( 11, p.min, 0x82dc75c0, 0x82dc75c0, 0x7a08f69a ); # negative-positive

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 12, p.min, 50,  50,  51 );
  TEST_RR_SRC2_EQ_DEST( 13, p.min, -7,  210, -7 );

  TEST_RR_SRC12_EQ_DEST( 14, p.min, -5, -5 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 15, 0, p.min, 11,  53, 11 );
  TEST_RR_DEST_BYPASS( 16, 1, p.min, -72, 11, -72 );
  TEST_RR_DEST_BYPASS( 17, 2, p.min, 11,  15, 11 );

  TEST_RR_SRC12_BYPASS( 18, 0, 0, p.min, 2,   13, 2 );
  TEST_RR_SRC12_BYPASS( 19, 0, 1, p.min, -5,  14, -5 );
  TEST_RR_SRC12_BYPASS( 20, 0, 2, p.min, 1,   15, 1 );
  TEST_RR_SRC12_BYPASS( 21, 1, 0, p.min, 12,  13, 12 );
  TEST_RR_SRC12_BYPASS( 22, 1, 1, p.min, 0,   14, 0 );
  TEST_RR_SRC12_BYPASS( 23, 2, 0, p.min, -15, 15, -15 );

  TEST_RR_SRC21_BYPASS( 24, 0, 0, p.min, 2,   13, 2 );
  TEST_RR_SRC21_BYPASS( 25, 0, 1, p.min, -5,  14, -5 );
  TEST_RR_SRC21_BYPASS( 26, 0, 2, p.min, 1,   15, 1 );
  TEST_RR_SRC21_BYPASS( 27, 1, 0, p.min, 12,  13, 12 );
  TEST_RR_SRC21_BYPASS( 28, 1, 1, p.min, 0,   14, 0 );
  TEST_RR_SRC21_BYPASS( 29, 2, 0, p.min, -15, 15, -15 );

  TEST_RR_ZEROSRC1( 30, p.min, 0, 15 );
  TEST_RR_ZEROSRC2( 31, p.min, -32, -32 );
  TEST_RR_ZEROSRC12( 32, p.min, 0 );

  TEST_RR_ZERODEST( 38, p.min, -16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
