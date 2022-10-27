# See LICENSE for license details.

#*****************************************************************************
# pv_pack.S
#-----------------------------------------------------------------------------
#
# Test pv.pack instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.pack.h
  TEST_RR_OP(  2, pv.pack.h, 0x00000000, 0x00003F6E, 0x000026D0 );
  TEST_RR_OP(  3, pv.pack.h, 0x511BEB39, 0x511B0706, 0xEB397322 );
  TEST_RR_OP(  4, pv.pack.h, 0x9D2D5C71, 0x9D2D15F2, 0x5C71278E );
  TEST_RR_OP(  5, pv.pack.h, 0x48872C48, 0x4887D28E, 0x2C487E80 );
  TEST_RR_OP(  6, pv.pack.h, 0xADE8D26A, 0xADE8E999, 0xD26AD68F );
  TEST_RR_OP(  7, pv.pack.h, 0xEFB66BF3, 0xEFB6AF79, 0x6BF30059 );
  TEST_RR_OP(  8, pv.pack.h, 0x5BBBB7FE, 0x5BBB1058, 0xB7FED864 );
  TEST_RR_OP(  9, pv.pack.h, 0x7292FDC2, 0x7292CF23, 0xFDC2EA55 );
  TEST_RR_OP( 10, pv.pack.h, 0x32CB6DB6, 0x32CBBE72, 0x6DB6060F );
  TEST_RR_OP( 11, pv.pack.h, 0xCB1900BC, 0xCB19A2A3, 0x00BCDD22 );

  #-------------------------------------------------------------
  # Source/Destination tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_SRC1_EQ_DEST,
  # TEST_RRR_SRC2_EQ_DEST, TEST_RRR_SRC12_EQ_DEST

  #-------------------------------------------------------------
  # Bypassing tests
  #-------------------------------------------------------------

  # TODO(smazzola):
  # for reg-reg-reg instructions TEST_RRR_DEST_BYPASS,
  # TEST_RRR_SRC12_BYPASS, TEST_RRR_SRC21_BYPASS, TEST_RRR_SRC3_BYPASS,
  # TEST_RRR_ZEROSRC1, TEST_RRR_ZEROSRC2, TEST_RRR_ZEROSRC3,
  # TEST_RRR_ZEROSRC12, TEST_RRR_ZEROSRC123, TEST_RRR_ZERODEST

  TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END
