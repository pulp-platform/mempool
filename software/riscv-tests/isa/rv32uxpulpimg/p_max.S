# See LICENSE for license details.

#*****************************************************************************
# p_max.S
#-----------------------------------------------------------------------------
#
# Test p.max instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.max, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.max, 0x00000000, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.max, 0x00000000, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.max, 0xffffffff, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.max, 0x1c38b1ff, 0x1c38b1ff, 0x06959b41 ); # positive-positive, max is rs1
  TEST_RR_OP( 7, p.max, 0x45cb9da6, 0x1ba104e1, 0x45cb9da6 ); # positive-positive, max is rs2
  TEST_RR_OP( 8, p.max, 0xa63ca8ee, 0xa63ca8ee, 0x8b53f386 ); # negative-negative, max is rs1
  TEST_RR_OP( 9, p.max, 0xf9fa7220, 0xf9177fa0, 0xf9fa7220 ); # negative-negative, max is rs2

  TEST_RR_OP( 10, p.max, 0x1b273d69, 0x1b273d69, 0xfad71033 ); # positive-negative
  TEST_RR_OP( 11, p.max, 0x05cb9da6, 0xdb4e653b, 0x05cb9da6 ); # negative-positive

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 12, p.max, 51,  50,  51 );
  TEST_RR_SRC2_EQ_DEST( 13, p.max, 210, 210, -7 );

  TEST_RR_SRC12_EQ_DEST( 14, p.max, 101, 101 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 15, 0, p.max, 53, 53, 11 );
  TEST_RR_DEST_BYPASS( 16, 1, p.max, 11, 11, -72 );
  TEST_RR_DEST_BYPASS( 17, 2, p.max, 15, 15, 11 );

  TEST_RR_SRC12_BYPASS( 18, 0, 0, p.max, 13, 13, 11 );
  TEST_RR_SRC12_BYPASS( 19, 0, 1, p.max, 14, 14, 11 );
  TEST_RR_SRC12_BYPASS( 20, 0, 2, p.max, 15, 15, 11 );
  TEST_RR_SRC12_BYPASS( 21, 1, 0, p.max, 13, 13, 11 );
  TEST_RR_SRC12_BYPASS( 22, 1, 1, p.max, 14, 14, 11 );
  TEST_RR_SRC12_BYPASS( 23, 2, 0, p.max, 15, 15, 11 );

  TEST_RR_SRC21_BYPASS( 24, 0, 0, p.max, 13, 13, 11 );
  TEST_RR_SRC21_BYPASS( 25, 0, 1, p.max, 14, 14, 11 );
  TEST_RR_SRC21_BYPASS( 26, 0, 2, p.max, 15, 15, 11 );
  TEST_RR_SRC21_BYPASS( 27, 1, 0, p.max, 13, 13, 11 );
  TEST_RR_SRC21_BYPASS( 28, 1, 1, p.max, 14, 14, 11 );
  TEST_RR_SRC21_BYPASS( 29, 2, 0, p.max, 15, 15, 11 );

  TEST_RR_ZEROSRC1( 30, p.max, 15, 15 );
  TEST_RR_ZEROSRC2( 31, p.max, 0, -32 );
  TEST_RR_ZEROSRC12( 32, p.max, 0 );

  TEST_RR_ZERODEST( 33, p.max, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
