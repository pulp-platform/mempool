# See LICENSE for license details.

#*****************************************************************************
# pv_sdotup.S
#-----------------------------------------------------------------------------
#
# Test pv.sdotup instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.sdotup.h
  TEST_RRR_OP( 2, pv.sdotup.h, 0xAFDDAF48, 0xFE67FB1A, 0x50E4DE57, 0x856509B6 );
  TEST_RRR_OP( 3, pv.sdotup.h, 0xF5942DA6, 0xADBC1E09, 0xA2C806FA, 0x8649EFFC );
  TEST_RRR_OP( 4, pv.sdotup.h, 0x71B65945, 0x3FDAEFE7, 0x7BA5CB0F, 0x9495383A );
  # pv.sdotup.sc.h
  TEST_RRR_OP( 5, pv.sdotup.sc.h, 0x06614853, 0x5E5C31BF, 0xCB24C409, 0x98078B60 );
  TEST_RRR_OP( 6, pv.sdotup.sc.h, 0x0146856D, 0xEC042250, 0x230A4695, 0xB6BE3689 );
  TEST_RRR_OP( 7, pv.sdotup.sc.h, 0xB607DEC3, 0x6BF5D085, 0x9AB012EF, 0x9E9FD4DD );
  # pv.sdotup.sci.h
  TEST_RR_UIMM6_OP(  8, pv.sdotup.sci.h, 0x6AC13EBF, 0x36D2FEAA, 17, 0x6AACB183 );
  TEST_RR_UIMM6_OP(  9, pv.sdotup.sci.h, 0xA622E695, 0x6752FECB,  2, 0xA6201A5B );
  TEST_RR_UIMM6_OP( 10, pv.sdotup.sci.h, 0x969DC76B, 0x9747CFF5, 11, 0x968E57D7 );
  # pv.sdotup.b
  TEST_RRR_OP( 11, pv.sdotup.b, 0x6BF9EC16, 0xEB8A58F5, 0xCAECEE54, 0x6BF8113C );
  TEST_RRR_OP( 12, pv.sdotup.b, 0x5D2493A6, 0x47665939, 0x9E989665, 0x5D23E0A1 );
  TEST_RRR_OP( 13, pv.sdotup.b, 0xC511F34F, 0x79D072B4, 0x5B8B4327, 0xC5111E1A );
  # pv.sdotup.sc.b
  TEST_RRR_OP( 14, pv.sdotup.sc.b, 0x7C691AEB, 0x6F622436, 0x1E1E694D, 0x7C68C0FC );
  TEST_RRR_OP( 15, pv.sdotup.sc.b, 0xAC5302E2, 0x77B8759A, 0xC1056E73, 0xAC520108 );
  TEST_RRR_OP( 16, pv.sdotup.sc.b, 0xAEA211C3, 0x74740933, 0xF898DF1E, 0xAEA1EF8B );
  # pv.sdotup.sci.b
  TEST_RR_UIMM6_OP( 17, pv.sdotup.sci.b, 0x86CD943A, 0x4CD92920, 11, 0x86CD8480 );
  TEST_RR_UIMM6_OP( 18, pv.sdotup.sci.b, 0x8239C123, 0xAFCE7172, 14, 0x82399FE3 );
  TEST_RR_UIMM6_OP( 19, pv.sdotup.sci.b, 0x3F753AE8, 0xDB25ABAA,  7, 0x3F752A95 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_SRC1_EQ_DEST,
  # TEST_RRR_SRC2_EQ_DEST, TEST_RRR_SRC12_EQ_DEST
  # for reg-uimm6-reg instructions *macros still to be written*

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_DEST_BYPASS,
  # TEST_RRR_SRC12_BYPASS, TEST_RRR_SRC21_BYPASS, TEST_RRR_SRC3_BYPASS,
  # TEST_RRR_ZEROSRC1, TEST_RRR_ZEROSRC2, TEST_RRR_ZEROSRC3,
  # TEST_RRR_ZEROSRC12, TEST_RRR_ZEROSRC123, TEST_RRR_ZERODEST
  # for reg-uimm6-reg instructions *macros still to be written*

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
