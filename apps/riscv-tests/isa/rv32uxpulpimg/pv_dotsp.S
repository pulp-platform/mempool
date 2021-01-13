# See LICENSE for license details.

#*****************************************************************************
# pv_dotsp.S
#-----------------------------------------------------------------------------
#
# Test pv.dotsp instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.dotsp.h
  TEST_RR_OP( 2, pv.dotsp.h, 0x0023A592, 0xFE67FB1A, 0x50E4DE57 );
  TEST_RR_OP( 3, pv.dotsp.h, 0x1EC63DAA, 0xADBC1E09, 0xA2C806FA );
  TEST_RR_OP( 4, pv.dotsp.h, 0x222B210B, 0x3FDAEFE7, 0x7BA5CB0F );
  # pv.dotsp.sc.h
  TEST_RR_OP( 5, pv.dotsp.sc.h, 0xDE3EBCF3, 0x5E5C31BF, 0xCB24C409 );
  TEST_RR_OP( 6, pv.dotsp.sc.h, 0x03F34EE4, 0xEC042250, 0x230A4695 );
  TEST_RR_OP( 7, pv.dotsp.sc.h, 0x047909E6, 0x6BF5D085, 0x9AB012EF );
  # pv.dotsp.sci.h
  TEST_SIMM6_OP(  8, pv.dotsp.sci.h, 0xFFFD1338, 0x36D2FEAA, -14 );
  TEST_SIMM6_OP(  9, pv.dotsp.sci.h, 0xFFFC68FB, 0x6752FECB,  -9 );
  TEST_SIMM6_OP( 10, pv.dotsp.sci.h, 0x000098C4, 0x9747CFF5,  -1 );
  # pv.dotsp.b
  TEST_RR_OP( 11, pv.dotsp.b, 0x000003DA, 0xEB8A58F5, 0xCAECEE54 );
  TEST_RR_OP( 12, pv.dotsp.b, 0xFFFFAD05, 0x47665939, 0x9E989665 );
  TEST_RR_OP( 13, pv.dotsp.b, 0x00005335, 0x79D072B4, 0x5B8B4327 );
  # pv.dotsp.sc.b
  TEST_RR_OP( 14, pv.dotsp.sc.b, 0x000059EF, 0x6F622436, 0x1E1E694D );
  TEST_RR_OP( 15, pv.dotsp.sc.b, 0x00001BDA, 0x77B8759A, 0xC1056E73 );
  TEST_RR_OP( 16, pv.dotsp.sc.b, 0x00002238, 0x74740933, 0xF898DF1E );
  # pv.dotsp.sci.b
  TEST_SIMM6_OP( 17, pv.dotsp.sci.b, 0x0000006E, 0x4CD92920,  1 );
  TEST_SIMM6_OP( 18, pv.dotsp.sci.b, 0xFFFFFE20, 0xAFCE7172, -5 );
  TEST_SIMM6_OP( 19, pv.dotsp.sci.b, 0xFFFFF9FD, 0xDB25ABAA,  9 );

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
