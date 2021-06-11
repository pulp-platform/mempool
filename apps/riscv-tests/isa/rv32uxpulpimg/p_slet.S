# See LICENSE for license details.

#*****************************************************************************
# p_slet.S
#-----------------------------------------------------------------------------
#
# Test p.slet instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.slet, 1, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.slet, 0, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.slet, 1, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.slet, 1, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.slet, 1, 0x384122e8, 0x70085691 ); # positive-positive, min is rs1
  TEST_RR_OP( 7, p.slet, 0, 0x7ab39050, 0x6479b271 ); # positive-positive, min is rs2
  TEST_RR_OP( 8, p.slet, 1, 0x8a7e0ad8, 0xb4635cea ); # negative-negative, min is rs1
  TEST_RR_OP( 9, p.slet, 0, 0xf0c13aa0, 0xe6fa0f05 ); # negative-negative, min is rs2

  TEST_RR_OP( 10, p.slet, 0, 0x76ddc053, 0xa4d42e72 ); # positive-negative
  TEST_RR_OP( 11, p.slet, 1, 0x82cd76c0, 0x0a08f69a ); # negative-positive

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 12, p.slet, 1,  50,  51 );
  TEST_RR_SRC2_EQ_DEST( 13, p.slet, 0,  210, -7 );

  TEST_RR_SRC12_EQ_DEST( 14, p.slet, 1, -5 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 15, 0, p.slet, 0,  53, 11 );
  TEST_RR_DEST_BYPASS( 16, 1, p.slet, 1, -72,  3 );
  TEST_RR_DEST_BYPASS( 17, 2, p.slet, 0,  15, 11 );

  TEST_RR_SRC12_BYPASS( 18, 0, 0, p.slet, 1,   1,  2 );
  TEST_RR_SRC12_BYPASS( 19, 0, 1, p.slet, 0,  14, -5 );
  TEST_RR_SRC12_BYPASS( 20, 0, 2, p.slet, 0,  15,  1 );
  TEST_RR_SRC12_BYPASS( 21, 1, 0, p.slet, 1,   3, 12 );
  TEST_RR_SRC12_BYPASS( 22, 1, 1, p.slet, 0,  14,  0 );
  TEST_RR_SRC12_BYPASS( 23, 2, 0, p.slet, 1, -15, 15 );

  TEST_RR_SRC21_BYPASS( 24, 0, 0, p.slet, 0, 13,   2 );
  TEST_RR_SRC21_BYPASS( 25, 0, 1, p.slet, 1, -5,  -5 );
  TEST_RR_SRC21_BYPASS( 26, 0, 2, p.slet, 0, 15,   1 );
  TEST_RR_SRC21_BYPASS( 27, 1, 0, p.slet, 1, 10,  12 );
  TEST_RR_SRC21_BYPASS( 28, 1, 1, p.slet, 1,  0,  14 );
  TEST_RR_SRC21_BYPASS( 29, 2, 0, p.slet, 1, 15,  15 );

  TEST_RR_ZEROSRC1( 30, p.slet, 1, 15 );
  TEST_RR_ZEROSRC2( 31, p.slet, 0, 32 );
  TEST_RR_ZEROSRC12( 32, p.slet, 1 );

  TEST_RR_ZERODEST( 33, p.slet, -16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
