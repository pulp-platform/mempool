# See LICENSE for license details.

#*****************************************************************************
# pv_maxu.S
#-----------------------------------------------------------------------------
#
# Test pv.maxu instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.maxu.h
  TEST_RR_OP( 2, pv.maxu.h, 0xBA529136, 0x3C369136, 0xBA524CAE );
  TEST_RR_OP( 3, pv.maxu.h, 0xC9E65AD2, 0xC9E60677, 0x00145AD2 );
  TEST_RR_OP( 4, pv.maxu.h, 0x42D67990, 0x42D67990, 0x244A0E31 );
  # pv.maxu.sc.h
  TEST_RR_OP( 5, pv.maxu.sc.h, 0x36D0CB1F, 0x36D0CB1F, 0x426D0434 );
  TEST_RR_OP( 6, pv.maxu.sc.h, 0xAE6DE3C7, 0xAE6DE3C7, 0x6ACB58AD );
  TEST_RR_OP( 7, pv.maxu.sc.h, 0xB6CDD3B0, 0xB6CDD3B0, 0x1CF29759 );
  # pv.maxu.sci.h
  TEST_UIMM6_OP(  8, pv.maxu.sci.h, 0xF503CA6A, 0xF503CA6A, 11 );
  TEST_UIMM6_OP(  9, pv.maxu.sci.h, 0x6781179C, 0x6781179C, 11 );
  TEST_UIMM6_OP( 10, pv.maxu.sci.h, 0xB778D8A3, 0xB778D8A3, 11 );
  # pv.maxu.b
  TEST_RR_OP( 11, pv.maxu.b, 0x17F9C1D2, 0x0DF91FD2, 0x1703C18D );
  TEST_RR_OP( 12, pv.maxu.b, 0xD04FEFA4, 0x434FEFA4, 0xD032B42E );
  TEST_RR_OP( 13, pv.maxu.b, 0x8A95BFF2, 0x56955708, 0x8A08BFF2 );
  # pv.maxu.sc.b
  TEST_RR_OP( 14, pv.maxu.sc.b, 0xE8E8E8E8, 0x318C6A64, 0x82B8BEE8 );
  TEST_RR_OP( 15, pv.maxu.sc.b, 0xDFE73926, 0xDFE73909, 0xBFC58126 );
  TEST_RR_OP( 16, pv.maxu.sc.b, 0x9DF09D9D, 0x6FF07641, 0x5689109D );
  # pv.maxu.sci.b
  TEST_UIMM6_OP( 17, pv.maxu.sci.b, 0x0B7062D8, 0x0A7062D8, 11 );
  TEST_UIMM6_OP( 18, pv.maxu.sci.b, 0x0B469D5D, 0x07469D5D, 11 );
  TEST_UIMM6_OP( 19, pv.maxu.sci.b, 0x4E875E27, 0x4E875E27, 11 );

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
