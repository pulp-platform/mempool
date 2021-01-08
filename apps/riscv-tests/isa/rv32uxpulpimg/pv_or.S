# See LICENSE for license details.

#*****************************************************************************
# pv_or.S
#-----------------------------------------------------------------------------
#
# Test pv.or instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.or.h
  TEST_RR_OP( 2, pv.or.h, 0xDFEFB3F3, 0x9E678370, 0x418EB1F3 );
  TEST_RR_OP( 3, pv.or.h, 0x7EFFDD7D, 0x727D5079, 0x7C968D05 );
  TEST_RR_OP( 4, pv.or.h, 0x5FAEEFD9, 0x4BAEA991, 0x1604EFD9 );
  # pv.or.sc.h
  TEST_RR_OP( 5, pv.or.sc.h, 0x7FB2EFF1, 0x5782C951, 0x886D2FB0 );
  TEST_RR_OP( 6, pv.or.sc.h, 0x7F9E6FF9, 0x5E0E04F9, 0x248B6F98 );
  TEST_RR_OP( 7, pv.or.sc.h, 0xBD9BBD4B, 0x85998C42, 0xD1F2B90B );
  # pv.or.sci.h
  TEST_UIMM6_OP(  8, pv.or.sci.h, 0x4F6F5CBF, 0x4F645CB5, 11 );
  TEST_UIMM6_OP(  9, pv.or.sci.h, 0x34DF2B7B, 0x34DD2B73, 11 );
  TEST_UIMM6_OP( 10, pv.or.sci.h, 0xE73F5DEF, 0xE73D5DE5, 11 );
  # pv.or.b
  TEST_RR_OP( 11, pv.or.b, 0xFDFAFC34, 0x25AA9830, 0xD8706434 );
  TEST_RR_OP( 12, pv.or.b, 0x9C7BF5EF, 0x9C41746A, 0x003BC1ED );
  TEST_RR_OP( 13, pv.or.b, 0x7BEBAEFF, 0x7B4BA8E2, 0x1BA3263F );
  # pv.or.sc.b
  TEST_RR_OP( 14, pv.or.sc.b, 0xFFF7B7B7, 0xFDE72320, 0x26977A97 );
  TEST_RR_OP( 15, pv.or.sc.b, 0xFFD5F5FD, 0xEA55E02C, 0x0D23AFD5 );
  TEST_RR_OP( 16, pv.or.sc.b, 0xDBDFFBD3, 0x9B8E6BC3, 0xCF31CDD3 );
  # pv.or.sci.b
  TEST_UIMM6_OP( 17, pv.or.sci.b, 0xCBCF2F9B, 0xC2CC2499, 11 );
  TEST_UIMM6_OP( 18, pv.or.sci.b, 0x3BEF1BEB, 0x33EE13E0, 11 );
  TEST_UIMM6_OP( 19, pv.or.sci.b, 0xFB5B5BEF, 0xF05252EE, 11 );

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
