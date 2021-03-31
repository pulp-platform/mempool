# See LICENSE for license details.

#*****************************************************************************
# pv_avgu.S
#-----------------------------------------------------------------------------
#
# Test pv.avgu instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.avgu.h
  TEST_RR_OP( 2, pv.avgu.h, 0x627F5574, 0xA12DA561, 0x23D10588 );
  TEST_RR_OP( 3, pv.avgu.h, 0x5F5E7CE3, 0x979062E4, 0x272C96E3 );
  TEST_RR_OP( 4, pv.avgu.h, 0x6D64331C, 0xF472E6FA, 0xE6567F3F );
  # pv.avgu.sc.h
  TEST_RR_OP( 5, pv.avgu.sc.h, 0x0CED14D1, 0xD924E8ED, 0xFFB240B6 );
  TEST_RR_OP( 6, pv.avgu.sc.h, 0x127F3F7B, 0x7447CE40, 0x64E4B0B7 );
  TEST_RR_OP( 7, pv.avgu.sc.h, 0x737C50C4, 0x7D7C380C, 0xB749697C );
  # pv.avgu.sci.h
  TEST_UIMM6_OP(  8, pv.avgu.sci.h, 0x76BB744A, 0xED6BE88A, 11 );
  TEST_UIMM6_OP(  9, pv.avgu.sci.h, 0x3BD96A9F, 0x77A8D534, 11 );
  TEST_UIMM6_OP( 10, pv.avgu.sci.h, 0x551A6EC8, 0xAA29DD86, 11 );
  # pv.avgu.b
  TEST_RR_OP( 11, pv.avgu.b, 0x366D332C, 0x8F75F8E9, 0xDD666F70 );
  TEST_RR_OP( 12, pv.avgu.b, 0x166D3707, 0x5F0C48DF, 0xCECE2730 );
  TEST_RR_OP( 13, pv.avgu.b, 0x13390E74, 0x2D0C048B, 0xFA67185E );
  # pv.avgu.sc.b
  TEST_RR_OP( 14, pv.avgu.sc.b, 0x20102F22, 0xFDDD1B00, 0x65EACB44 );
  TEST_RR_OP( 15, pv.avgu.sc.b, 0x79130A10, 0x2156444F, 0xAF0796D1 );
  TEST_RR_OP( 16, pv.avgu.sc.b, 0x44260042, 0x591DD256, 0xFBAE832F );
  # pv.avgu.sci.b
  TEST_UIMM6_OP( 17, pv.avgu.sci.b, 0x016B6549, 0xF7CBBF88, 11 );
  TEST_UIMM6_OP( 18, pv.avgu.sci.b, 0x742F1E50, 0xDE543195, 11 );
  TEST_UIMM6_OP( 19, pv.avgu.sci.b, 0x34686166, 0x5EC5B7C1, 11 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_SRC1_EQ_DEST,
  # TEST_RR_SRC2_EQ_DEST, TEST_RR_SRC12_EQ_DEST
  # for register-simm6 instructions TEST_UIMM6_SRC1_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for register-register instructions TEST_RR_DEST_BYPASS,
  # TEST_RR_SRC12_BYPASS, TEST_RR_SRC21_BYPASS, TEST_RR_ZEROSRC1,
  # TEST_RR_ZEROSRC2, TEST_RR_ZEROSRC12, TEST_RR_ZERODEST
  # for register-simm6 instructions TEST_UIMM6_DEST_BYPASS,
  # TEST_UIMM6_SRC1_BYPASS, TEST_UIMM6_ZEROSRC1, TEST_UIMM6_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
