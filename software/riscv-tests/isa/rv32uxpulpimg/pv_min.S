# See LICENSE for license details.

#*****************************************************************************
# pv_min.S
#-----------------------------------------------------------------------------
#
# Test pv.min instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV32U
RVTEST_CODE_BEGIN

  #-------------------------------------------------------------
  # Arithmetic tests
  #-------------------------------------------------------------

  # pv.min.h
  TEST_RR_OP( 2, pv.min.h, 0x82E7A6AB, 0x8A92A6AB, 0x82E77B73 );
  TEST_RR_OP( 3, pv.min.h, 0xE3770915, 0xE37773E8, 0x44330915 );
  TEST_RR_OP( 4, pv.min.h, 0x85B0BA95, 0x85B0E12E, 0x6CA1BA95 );
  # pv.min.sc.h
  TEST_RR_OP( 5, pv.min.sc.h, 0x33A388EB, 0x33A388EB, 0xA73B6225 );
  TEST_RR_OP( 6, pv.min.sc.h, 0xB2D1B2D1, 0x6C255634, 0xC06DB2D1 );
  TEST_RR_OP( 7, pv.min.sc.h, 0xED24CC32, 0xED24CC32, 0x20DD20AE );
  # pv.min.sci.h
  TEST_SIMM6_OP(  8, pv.min.sci.h, 0x000BABA8, 0x3116ABA8, 11 );
  TEST_SIMM6_OP(  9, pv.min.sci.h, 0xF270FB23, 0xF270FB23, 11 );
  TEST_SIMM6_OP( 10, pv.min.sci.h, 0xF45DE902, 0xF45DE902, 11 );
  # pv.min.b
  TEST_RR_OP( 11, pv.min.b, 0x3BD1A58C, 0x3BF5A5CD, 0x59D1618C );
  TEST_RR_OP( 12, pv.min.b, 0x99C52CBA, 0xF4D42C6F, 0x99C57ABA );
  TEST_RR_OP( 13, pv.min.b, 0x13CB8AE9, 0x13CB8AE9, 0x47F8D538 );
  # pv.min.sc.b
  TEST_RR_OP( 14, pv.min.sc.b, 0xDCC161BB, 0xDCC161BB, 0x41A0EA7B );
  TEST_RR_OP( 15, pv.min.sc.b, 0x3059A553, 0x3059A553, 0xB80EA978 );
  TEST_RR_OP( 16, pv.min.sc.b, 0x97ECEFEF, 0x97EC4211, 0x8059FEEF );
  # pv.min.sci.b
  TEST_SIMM6_OP( 17, pv.min.sci.b, 0x0B0BB986, 0x732DB986, 11 );
  TEST_SIMM6_OP( 18, pv.min.sci.b, 0xF40B0BE7, 0xF47567E7, 11 );
  TEST_SIMM6_OP( 19, pv.min.sci.b, 0x0BF70B0B, 0x7DF77268, 11 );

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
