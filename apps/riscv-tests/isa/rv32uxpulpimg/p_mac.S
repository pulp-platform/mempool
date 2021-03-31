# See LICENSE for license details.

#*****************************************************************************
# p_mac.S
#-----------------------------------------------------------------------------
#
# Test p.mac instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_RRR_OP( 2, p.mac, 0x00000000, 0x00000000, 0x00000000, 0x00000000 )
  TEST_RRR_OP( 3, p.mac, 0xFFFFFFFF, 0x00000000, 0x00000000, 0xFFFFFFFF )
  TEST_RRR_OP( 4, p.mac, 0x00000000, 0x00000000, 0xFFFFFFFF, 0x00000000 )
  TEST_RRR_OP( 5, p.mac, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF, 0xFFFFFFFF )
  TEST_RRR_OP( 6, p.mac, 0x00000000, 0xFFFFFFFF, 0x00000000, 0x00000000 )
  TEST_RRR_OP( 7, p.mac, 0xFFFFFFFF, 0xFFFFFFFF, 0x00000000, 0xFFFFFFFF )
  TEST_RRR_OP( 8, p.mac, 0x00000001, 0xFFFFFFFF, 0xFFFFFFFF, 0x00000000 )
  TEST_RRR_OP( 9, p.mac, 0x00000000, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF )

  TEST_RRR_OP( 10, p.mac, 0x4CF50B3F, 0xB463DADE, 0x1C2D45F3, 0x67287485 )
  TEST_RRR_OP( 11, p.mac, 0x01C8425D, 0x5DE547E9, 0xBE923643, 0x20B94A62 )
  TEST_RRR_OP( 12, p.mac, 0x125000F5, 0xD5042C35, 0x113E2192, 0xD265F5BB )
  TEST_RRR_OP( 13, p.mac, 0x117DE9BB, 0x0762A9A5, 0xAB420127, 0x9B426C98 )

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_RRR_SRC1_EQ_DEST( 14, p.mac, 0x0CEE5928, 0x113E2192, 0x1C2D45F3 )
  TEST_RRR_SRC2_EQ_DEST( 15, p.mac, 0x1F280E82, 0x7E139C55, 0xBE923643 )

  TEST_RRR_SRC12_EQ_DEST( 16, p.mac, 0x22EE857E, 0x84BB8025 )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_RRR_DEST_BYPASS( 17, 0, p.mac,  5, 1, 2, 3 )
  TEST_RRR_DEST_BYPASS( 18, 1, p.mac, 26, 4, 5, 6 )
  TEST_RRR_DEST_BYPASS( 19, 2, p.mac, 65, 7, 8, 9 )

  TEST_RRR_SRC12_BYPASS( 20, 0, 0, p.mac,   5,  1,  2,  3 )
  TEST_RRR_SRC12_BYPASS( 21, 0, 1, p.mac,  26,  4,  5,  6 )
  TEST_RRR_SRC12_BYPASS( 22, 0, 2, p.mac,  65,  7,  8,  9 )
  TEST_RRR_SRC12_BYPASS( 23, 1, 0, p.mac,   5, -1, -2,  3 )
  TEST_RRR_SRC12_BYPASS( 24, 1, 1, p.mac,  14,  4,  5, -6 )
  TEST_RRR_SRC12_BYPASS( 25, 2, 0, p.mac, -47, -7,  8,  9 )

  TEST_RRR_SRC21_BYPASS( 26, 0, 0, p.mac,   5,  1,  2,  3 )
  TEST_RRR_SRC21_BYPASS( 27, 0, 1, p.mac,  26,  4,  5,  6 )
  TEST_RRR_SRC21_BYPASS( 28, 0, 2, p.mac,  65,  7,  8,  9 )
  TEST_RRR_SRC21_BYPASS( 29, 1, 0, p.mac,   5, -1, -2,  3 )
  TEST_RRR_SRC21_BYPASS( 30, 1, 1, p.mac,  14,  4,  5, -6 )
  TEST_RRR_SRC21_BYPASS( 31, 2, 0, p.mac, -47, -7,  8,  9 )

  TEST_RRR_SRC3_BYPASS( 32, 0, p.mac, 26,  4,  5, 6 )
  TEST_RRR_SRC3_BYPASS( 33, 1, p.mac, 65,  7,  8, 9 )
  TEST_RRR_SRC3_BYPASS( 34, 2, p.mac,  5, -1, -2, 3 )

  TEST_RRR_ZEROSRC1( 35, p.mac, 10, -5, 10 )
  TEST_RRR_ZEROSRC2( 36, p.mac,  7, 32,  7 )
  TEST_RRR_ZEROSRC3( 37, p.mac, -8, -1,  8 )

  TEST_RRR_ZEROSRC12( 38, p.mac, -3, -3 )

  TEST_RRR_ZEROSRC123( 39, p.mac, 0 )

  TEST_RRR_ZERODEST( 40, p.mac, 34, -10 )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
