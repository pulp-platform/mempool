# See LICENSE for license details.

#*****************************************************************************
# pv_max.S
#-----------------------------------------------------------------------------
#
# Test pv.max instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.max.h
  TEST_RR_OP( 2, pv.max.h, 0x731E1846, 0xF4D3B4D4, 0x731E1846 );
  TEST_RR_OP( 3, pv.max.h, 0x0E5963C7, 0x0E5963C7, 0xC078A04B );
  TEST_RR_OP( 4, pv.max.h, 0x10AF37F3, 0x10AF37F3, 0xA4DA964F );
  # pv.max.sc.h
  TEST_RR_OP( 5, pv.max.sc.h, 0xFDCCFDCC, 0xC86DA7A4, 0x5AC6FDCC );
  TEST_RR_OP( 6, pv.max.sc.h, 0x6F096F09, 0x1EBE021F, 0xAEAF6F09 );
  TEST_RR_OP( 7, pv.max.sc.h, 0x72AF72AF, 0xCD6ACE5B, 0xA0D172AF );
  # pv.max.sci.h
  TEST_SIMM6_OP(  8, pv.max.sci.h, 0x000B1FDD, 0xAD6D1FDD, 11 );
  TEST_SIMM6_OP(  9, pv.max.sci.h, 0x000B000B, 0xAAF6EBB0, 11 );
  TEST_SIMM6_OP( 10, pv.max.sci.h, 0x252B000B, 0x252BC255, 11 );
  # pv.max.b
  TEST_RR_OP( 11, pv.max.b, 0xF2402D09, 0xB040FD9D, 0xF2842D09 );
  TEST_RR_OP( 12, pv.max.b, 0x78652008, 0xD749FDBE, 0x78652008 );
  TEST_RR_OP( 13, pv.max.b, 0xC5755F6A, 0xC5755F6A, 0xAD1CD088 );
  # pv.max.sc.b
  TEST_RR_OP( 14, pv.max.sc.b, 0x75757575, 0x01B6C06B, 0xC1698275 );
  TEST_RR_OP( 15, pv.max.sc.b, 0x7B7B7B7B, 0x4A547B78, 0xCD4D377B );
  TEST_RR_OP( 16, pv.max.sc.b, 0x5D7B5D5F, 0x027B0E5F, 0x595E995D );
  # pv.max.sci.b
  TEST_SIMM6_OP( 17, pv.max.sci.b, 0x0B0B0B0B, 0xEB06FBAB, 11 );
  TEST_SIMM6_OP( 18, pv.max.sci.b, 0x56240B26, 0x56249726, 11 );
  TEST_SIMM6_OP( 19, pv.max.sci.b, 0x5F32211E, 0x5F32211E, 11 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_SRC1_EQ_DEST,
  # TEST_RR_SRC2_EQ_DEST, TEST_RR_SRC12_EQ_DEST
  # for register-simm6 instructions TEST_SIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_DEST_BYPASS,
  # TEST_RR_SRC12_BYPASS, TEST_RR_SRC21_BYPASS, TEST_RR_ZEROSRC1,
  # TEST_RR_ZEROSRC2, TEST_RR_ZEROSRC12, TEST_RR_ZERODEST
  # for register-simm6 instructions TEST_SIMM6_DEST_BYPASS,
  # TEST_SIMM6_SRC1_BYPASS, TEST_SIMM6_ZEROSRC1, TEST_SIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
