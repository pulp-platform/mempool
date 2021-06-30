# See LICENSE for license details.

#*****************************************************************************
# pv_sra.S
#-----------------------------------------------------------------------------
#
# Test pv.sra instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.sra.h
  TEST_RR_OP( 2, pv.sra.h, 0x2C4BFFF8, 0x5896C0A3, 0x0001000B );
  TEST_RR_OP( 3, pv.sra.h, 0x005E760F, 0x5E43760F, 0x00080000 );
  TEST_RR_OP( 4, pv.sra.h, 0x0059F46B, 0x166BA35F, 0x00060003 );
  # pv.sra.sc.h
  TEST_RR_OP( 5, pv.sra.sc.h, 0x00000005, 0x080A5F54, 0x000D000C );
  TEST_RR_OP( 6, pv.sra.sc.h, 0xFF0400FB, 0xE0871F6D, 0x00020005 );
  TEST_RR_OP( 7, pv.sra.sc.h, 0x00010000, 0x40FF2C98, 0x000B000E );
  # pv.sra.sci.h
  TEST_UIMM6_OP(  8, pv.sra.sci.h, 0xFFE70029, 0xCEB053F9, 9 );
  TEST_UIMM6_OP(  9, pv.sra.sci.h, 0xFFD5FFF8, 0xAA4AF03F, 9 );
  TEST_UIMM6_OP( 10, pv.sra.sci.h, 0x00340008, 0x68E511A2, 9 );
  # pv.sra.b
  TEST_RR_OP( 11, pv.sra.b, 0x08FF00F9, 0x11F61B9D, 0x01050704 );
  TEST_RR_OP( 12, pv.sra.b, 0xFCFCFFF3, 0x8FE3F89C, 0x05030603 );
  TEST_RR_OP( 13, pv.sra.b, 0x0096FFA3, 0x0296E1A3, 0x02000600 );
  # pv.sra.sc.b
  TEST_RR_OP( 14, pv.sra.sc.b, 0x66F6E2A1, 0x66F6E2A1, 0x01050600 );
  TEST_RR_OP( 15, pv.sra.sc.b, 0x0DFD1A13, 0x36F56B4D, 0x03040302 );
  TEST_RR_OP( 16, pv.sra.sc.b, 0x00000201, 0x16135625, 0x01040205 );
  # pv.sra.sci.b
  TEST_UIMM6_OP( 17, pv.sra.sci.b, 0xFCFC02FD, 0x848B57AD, 5 );
  TEST_UIMM6_OP( 18, pv.sra.sci.b, 0x02FE02FC, 0x40CD5290, 5 );
  TEST_UIMM6_OP( 19, pv.sra.sci.b, 0x02FCFF01, 0x549FFD20, 5 );

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
