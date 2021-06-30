# See LICENSE for license details.

#*****************************************************************************
# p_exthz.S
#-----------------------------------------------------------------------------
#
# Test p.exthz instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_R_OP( 2, p.exthz, 0x00000000, 0x00000000 );
  TEST_R_OP( 3, p.exthz, 0x0000ffff, 0xffffffff );

  TEST_R_OP( 4, p.exthz, 0x00000000, 0xffff0000 );
  TEST_R_OP( 5, p.exthz, 0x0000ffff, 0x0000ffff );

  TEST_R_OP( 6, p.exthz, 0x000068D3, 0x111468D3 );
  TEST_R_OP( 7, p.exthz, 0x0000E504, 0x8D34E504 );
  TEST_R_OP( 8, p.exthz, 0x00004A6A, 0xE7424A6A );
  TEST_R_OP( 9, p.exthz, 0x0000589B, 0x00DC589B );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_R_SRC1_EQ_DEST( 10, p.exthz, 0x000015DF, 0x8CE115DF )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_R_DEST_BYPASS( 11, 0, p.exthz, 0x0000F8D6, 0x252FF8D6 )
  TEST_R_DEST_BYPASS( 12, 1, p.exthz, 0x0000B24D, 0x65FDB24D )
  TEST_R_DEST_BYPASS( 13, 2, p.exthz, 0x0000306C, 0xD56D306C )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
