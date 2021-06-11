# See LICENSE for license details.

#*****************************************************************************
# p_maxu.S
#-----------------------------------------------------------------------------
#
# Test p.maxu instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RR_OP( 2, p.maxu, 0x00000000, 0x00000000, 0x00000000 );
  TEST_RR_OP( 3, p.maxu, 0xffffffff, 0x00000000, 0xffffffff );
  TEST_RR_OP( 4, p.maxu, 0xffffffff, 0xffffffff, 0x00000000 );
  TEST_RR_OP( 5, p.maxu, 0xffffffff, 0xffffffff, 0xffffffff );

  TEST_RR_OP( 6, p.maxu, 0x1c38b1ff, 0x1c38b1ff, 0x06959b41 );
  TEST_RR_OP( 7, p.maxu, 0xf9fa7220, 0xf9177fa0, 0xf9fa7220 );
  TEST_RR_OP( 8, p.maxu, 0xfad71033, 0x1b273d69, 0xfad71033 );
  TEST_RR_OP( 9, p.maxu, 0xdb4e653b, 0xdb4e653b, 0x05cb9da6 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RR_SRC1_EQ_DEST( 10, p.maxu, 51,  50,  51 );
  TEST_RR_SRC2_EQ_DEST( 11, p.maxu, 210, 210, 7 );

  TEST_RR_SRC12_EQ_DEST( 12, p.maxu, 101, 101 );

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RR_DEST_BYPASS( 13, 0, p.maxu, 53, 53, 11 );
  TEST_RR_DEST_BYPASS( 14, 1, p.maxu, 72, 11, 72 );
  TEST_RR_DEST_BYPASS( 15, 2, p.maxu, 15, 15, 11 );

  TEST_RR_SRC12_BYPASS( 16, 0, 0, p.maxu, 13, 13, 11 );
  TEST_RR_SRC12_BYPASS( 17, 0, 1, p.maxu, 14, 14, 11 );
  TEST_RR_SRC12_BYPASS( 18, 0, 2, p.maxu, 15, 15, 11 );
  TEST_RR_SRC12_BYPASS( 19, 1, 0, p.maxu, 13, 13, 11 );
  TEST_RR_SRC12_BYPASS( 20, 1, 1, p.maxu, 14, 14, 11 );
  TEST_RR_SRC12_BYPASS( 21, 2, 0, p.maxu, 15, 15, 11 );

  TEST_RR_SRC21_BYPASS( 22, 0, 0, p.maxu, 13, 13, 11 );
  TEST_RR_SRC21_BYPASS( 23, 0, 1, p.maxu, 14, 14, 11 );
  TEST_RR_SRC21_BYPASS( 24, 0, 2, p.maxu, 15, 15, 11 );
  TEST_RR_SRC21_BYPASS( 25, 1, 0, p.maxu, 13, 13, 11 );
  TEST_RR_SRC21_BYPASS( 26, 1, 1, p.maxu, 14, 14, 11 );
  TEST_RR_SRC21_BYPASS( 27, 2, 0, p.maxu, 15, 15, 11 );

  TEST_RR_ZEROSRC1( 28, p.maxu, 15, 15 );
  TEST_RR_ZEROSRC2( 29, p.maxu, 32, 32 );
  TEST_RR_ZEROSRC12( 30, p.maxu, 0 );

  TEST_RR_ZERODEST( 31, p.maxu, 16, 30 );

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
