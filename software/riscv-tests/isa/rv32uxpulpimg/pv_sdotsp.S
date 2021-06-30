# See LICENSE for license details.

#*****************************************************************************
# pv_sdotsp.S
#-----------------------------------------------------------------------------
#
# Test pv.sdotsp instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.sdotsp.h
  TEST_RRR_OP( 2, pv.sdotsp.h, 0x8588AF48, 0xFE67FB1A, 0x50E4DE57, 0x856509B6 );
  TEST_RRR_OP( 3, pv.sdotsp.h, 0xA5102DA6, 0xADBC1E09, 0xA2C806FA, 0x8649EFFC );
  TEST_RRR_OP( 4, pv.sdotsp.h, 0xB6C05945, 0x3FDAEFE7, 0x7BA5CB0F, 0x9495383A );
  # pv.sdotsp.sc.h
  TEST_RRR_OP( 5, pv.sdotsp.sc.h, 0x76464853, 0x5E5C31BF, 0xCB24C409, 0x98078B60 );
  TEST_RRR_OP( 6, pv.sdotsp.sc.h, 0xBAB1856D, 0xEC042250, 0x230A4695, 0xB6BE3689 );
  TEST_RRR_OP( 7, pv.sdotsp.sc.h, 0xA318DEC3, 0x6BF5D085, 0x9AB012EF, 0x9E9FD4DD );
  # pv.sdotsp.sci.h
  TEST_RR_SIMM6_OP(  8, pv.sdotsp.sci.h, 0x6AA9C4BB, 0x36D2FEAA, -14, 0x6AACB183 );
  TEST_RR_SIMM6_OP(  9, pv.sdotsp.sci.h, 0xA61C8356, 0x6752FECB,  -9, 0xA6201A5B );
  TEST_RR_SIMM6_OP( 10, pv.sdotsp.sci.h, 0x968EF09B, 0x9747CFF5,  -1, 0x968E57D7 );
  # pv.sdotsp.b
  TEST_RRR_OP( 11, pv.sdotsp.b, 0x6BF81516, 0xEB8A58F5, 0xCAECEE54, 0x6BF8113C );
  TEST_RRR_OP( 12, pv.sdotsp.b, 0x5D238DA6, 0x47665939, 0x9E989665, 0x5D23E0A1 );
  TEST_RRR_OP( 13, pv.sdotsp.b, 0xC511714F, 0x79D072B4, 0x5B8B4327, 0xC5111E1A );
  # pv.sdotsp.sc.b
  TEST_RRR_OP( 14, pv.sdotsp.sc.b, 0x7C691AEB, 0x6F622436, 0x1E1E694D, 0x7C68C0FC );
  TEST_RRR_OP( 15, pv.sdotsp.sc.b, 0xAC521CE2, 0x77B8759A, 0xC1056E73, 0xAC520108 );
  TEST_RRR_OP( 16, pv.sdotsp.sc.b, 0xAEA211C3, 0x74740933, 0xF898DF1E, 0xAEA1EF8B );
  # pv.sdotsp.sci.b
  TEST_RR_SIMM6_OP( 17, pv.sdotsp.sci.b, 0x86CD84EE, 0x4CD92920,  1, 0x86CD8480 );
  TEST_RR_SIMM6_OP( 18, pv.sdotsp.sci.b, 0x82399E03, 0xAFCE7172, -5, 0x82399FE3 );
  TEST_RR_SIMM6_OP( 19, pv.sdotsp.sci.b, 0x3F752492, 0xDB25ABAA,  9, 0x3F752A95 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_SRC1_EQ_DEST,
  # TEST_RRR_SRC2_EQ_DEST, TEST_RRR_SRC12_EQ_DEST
  # for reg-simm6-reg instructions *macros still to be written*

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_DEST_BYPASS,
  # TEST_RRR_SRC12_BYPASS, TEST_RRR_SRC21_BYPASS, TEST_RRR_SRC3_BYPASS,
  # TEST_RRR_ZEROSRC1, TEST_RRR_ZEROSRC2, TEST_RRR_ZEROSRC3,
  # TEST_RRR_ZEROSRC12, TEST_RRR_ZEROSRC123, TEST_RRR_ZERODEST
  # for reg-simm6-reg instructions *macros still to be written*

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
