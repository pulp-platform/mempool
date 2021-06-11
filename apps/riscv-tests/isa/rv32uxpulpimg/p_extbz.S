# See LICENSE for license details.

#*****************************************************************************
# p_extbz.S
#-----------------------------------------------------------------------------
#
# Test p.extbz instruction.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  TEST_R_OP( 2, p.extbz, 0x00000000, 0x00000000 );
  TEST_R_OP( 3, p.extbz, 0x000000ff, 0xffffffff );

  TEST_R_OP( 4, p.extbz, 0x00000000, 0xffffff00 );
  TEST_R_OP( 5, p.extbz, 0x000000ff, 0x000000ff );

  TEST_R_OP( 6, p.extbz, 0x000000B8, 0x6C187CB8 );
  TEST_R_OP( 7, p.extbz, 0x00000013, 0x336A1213 );
  TEST_R_OP( 8, p.extbz, 0x00000098, 0x54F68F98 );
  TEST_R_OP( 9, p.extbz, 0x00000083, 0x8A874D83 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  TEST_R_SRC1_EQ_DEST( 10, p.extbz, 0x0000003F, 0x95EBD93F )

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  TEST_R_DEST_BYPASS( 11, 0, p.extbz, 0x00000033, 0x93A7EC33 )
  TEST_R_DEST_BYPASS( 12, 1, p.extbz, 0x00000079, 0x6D4E7B79 )
  TEST_R_DEST_BYPASS( 13, 2, p.extbz, 0x0000000A, 0x2AA91C0A )

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
