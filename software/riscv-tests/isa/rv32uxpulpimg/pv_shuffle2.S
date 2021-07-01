# See LICENSE for license details.

#*****************************************************************************
# pv_shuffle2.S
#-----------------------------------------------------------------------------
#
# Test pv.shuffle2 instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.shuffle2.h
  TEST_RRR_OP(  2, pv.shuffle2.h, 0xABD0A85B, 0xABD03F6E, 0x1D4B26D0, 0xF0C3A85B );
  TEST_RRR_OP(  3, pv.shuffle2.h, 0x93A60706, 0x511B0706, 0xEB397322, 0x93A613C6 );
  TEST_RRR_OP(  4, pv.shuffle2.h, 0x2BCE15F2, 0x9D2D15F2, 0x5C71278E, 0x2BCEDA18 );
  TEST_RRR_OP(  5, pv.shuffle2.h, 0x2C48AA34, 0x2C48AA34, 0x4887D28E, 0x55247E80 );
  TEST_RRR_OP(  6, pv.shuffle2.h, 0xE999ADE8, 0xADE8E999, 0xD26AD68F, 0x23A14961 );
  TEST_RRR_OP(  7, pv.shuffle2.h, 0x0059517C, 0x6BF30059, 0xEFB6AF79, 0x517C1495 );
  TEST_RRR_OP(  8, pv.shuffle2.h, 0xB7FEA035, 0xB7FED864, 0x5BBB1058, 0x4583A035 );
  TEST_RRR_OP(  9, pv.shuffle2.h, 0xEA55FDC2, 0xFDC2EA55, 0x7292CF23, 0x4F82A53E );
  TEST_RRR_OP( 10, pv.shuffle2.h, 0xBE7232CB, 0x32CBBE72, 0x6DB6060F, 0x22C33B63 );
  TEST_RRR_OP( 11, pv.shuffle2.h, 0x4389A2A3, 0xCB19A2A3, 0x00BCDD22, 0xFB744389 );
  # pv.shuffle2.b
  TEST_RRR_OP( 12, pv.shuffle2.b, 0xDAD9ECA3, 0x35A309D9, 0x8AE410B6, 0x22DA0BEC );
  TEST_RRR_OP( 13, pv.shuffle2.b, 0x0EF485F4, 0xCA850EB8, 0x256B969B, 0xF438D1D7 );
  TEST_RRR_OP( 14, pv.shuffle2.b, 0x1414E4C0, 0xE433C0A1, 0xC8381F65, 0xAC7DBC14 );
  TEST_RRR_OP( 15, pv.shuffle2.b, 0x81676762, 0x36DE6217, 0xC98AEA7D, 0x9D6781F4 );
  TEST_RRR_OP( 16, pv.shuffle2.b, 0xD80DD8B4, 0xD8CE132C, 0x67D8BF89, 0x166FB40D );
  TEST_RRR_OP( 17, pv.shuffle2.b, 0x7B9E0404, 0x657BF4D6, 0x06DB0232, 0x9E049D7E );
  TEST_RRR_OP( 18, pv.shuffle2.b, 0xD15526EE, 0x617EEED1, 0xE4D33275, 0x55264DEE );
  TEST_RRR_OP( 19, pv.shuffle2.b, 0x73AB4CAB, 0x43AB21CB, 0x4B2EC0BE, 0x7306984C );
  TEST_RRR_OP( 20, pv.shuffle2.b, 0x5235C41D, 0x052B5263, 0x85BB52D0, 0x35C4A31D );
  TEST_RRR_OP( 21, pv.shuffle2.b, 0xF1E0F194, 0xFFABF194, 0x35CBE594, 0xE0A7A1D1 );

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
