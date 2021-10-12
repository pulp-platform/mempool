# See LICENSE for license details.

#*****************************************************************************
# lrsr.S
#-----------------------------------------------------------------------------
#
# Test LR/SC instructions.
#

#include "riscv_test.h"
#include "test_macros.h"

RVTEST_RV64U
RVTEST_CODE_BEGIN

# make sure that sc without a reservation fails.
TEST_CASE( 2, a4, 1, \
  la a0, foo; \
  li a5, 0xdeadbeef; \
  sc.w a4, a5, (a0); \
)

# make sure the failing sc did not commit into memory
TEST_CASE( 3, a4, 0, \
  lw a4, foo; \
)

# make sure that sc with the wrong reservation fails.
# TODO is this actually mandatory behavior?
TEST_CASE( 4, a4, 1, \
  la a0, foo; \
  la a1, fooTest3; \
  lr.w a1, (a1); \
  sc.w a4, a1, (a0); \
)

TEST_PASSFAIL

RVTEST_CODE_END

  .data
RVTEST_DATA_BEGIN

  TEST_DATA

RVTEST_DATA_END

  .bss
  .align 3
foo:
  .dword 0
fooTest3:
  .dword 0
