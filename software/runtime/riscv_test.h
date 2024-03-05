// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// clang-format off

#ifndef _ENV_PHYSICAL_SINGLE_CORE_H
#define _ENV_PHYSICAL_SINGLE_CORE_H

#include "encoding.h"
#include "addrmap.h"

//-----------------------------------------------------------------------
// Begin Macro
//-----------------------------------------------------------------------

#define RVTEST_RV64U                                                           \
  .macro init;                                                                 \
  .endm

#define RVTEST_RV64UF                                                          \
  .macro init;                                                                 \
  RVTEST_FP_ENABLE;                                                            \
  .endm

#define RVTEST_RV32U                                                           \
  .macro init;                                                                 \
  .endm

#define RVTEST_RV32UF                                                          \
  .macro init;                                                                 \
  RVTEST_FP_ENABLE;                                                            \
  .endm

#define RVTEST_RV64M                                                           \
  .macro init;                                                                 \
  RVTEST_ENABLE_MACHINE;                                                       \
  .endm

#define RVTEST_RV64S                                                           \
  .macro init;                                                                 \
  RVTEST_ENABLE_SUPERVISOR;                                                    \
  .endm

#define RVTEST_RV32M                                                           \
  .macro init;                                                                 \
  RVTEST_ENABLE_MACHINE;                                                       \
  .endm

#define RVTEST_RV32S                                                           \
  .macro init;                                                                 \
  RVTEST_ENABLE_SUPERVISOR;                                                    \
  .endm

#define RVTEST_ENABLE_SUPERVISOR                                               \
  li a0, MSTATUS_MPP & (MSTATUS_MPP >> 1);                                     \
  csrs mstatus, a0;                                                            \
  li a0, SIP_SSIP | SIP_STIP;                                                  \
  csrs mideleg, a0;

#define RVTEST_ENABLE_MACHINE                                                  \
  li a0, MSTATUS_MPP;                                                          \
  csrs mstatus, a0;

#define RVTEST_FP_ENABLE

#define RISCV_MULTICORE_DISABLE                                                \
  csrr a0, mhartid;                                                            \
  bnez a0, _sleep;                                                             \


#define EXTRA_TVEC_USER
#define EXTRA_TVEC_MACHINE
#define EXTRA_INIT
#define EXTRA_INIT_TIMER

#define INTERRUPT_HANDLER j other_exception /* No interrupts should occur */

#define RVTEST_CODE_BEGIN                                                      \
        .section .text.init;                                                   \
        .align 6;                                                              \
        .globl _start;                                                         \
_start:                                                                        \
        /* reset vector */                                                     \
        j reset_vector;                                                        \
        .align 2;                                                              \
reset_vector:                                                                  \
        RISCV_MULTICORE_DISABLE;                                               \
        li TESTNUM, 0;                                                         \
        init;                                                                  \
        EXTRA_INIT;                                                            \
        EXTRA_INIT_TIMER;                                                      \
  //-----------------------------------------------------------------------
  // End Macro
  //-----------------------------------------------------------------------

#define RVTEST_CODE_END                                                        \
_eoc:                                                                          \
        li t0, (CONTROL_REGISTER_OFFSET + CONTROL_REGISTERS_EOC_REG_OFFSET);   \
        slli t1, a0, 1;                                                        \
        addi t1, t1, 1;                                                        \
        sw t1, 0(t0);                                                          \
_sleep:                                                                        \
        wfi;

//-----------------------------------------------------------------------
// Pass/Fail Macro
//-----------------------------------------------------------------------
#define TESTNUM gp

#define RVTEST_PASS                                                            \
        li a0, 0;                                                              \
        j _eoc;

#define RVTEST_FAIL                                                            \
        beqz TESTNUM, 1f;                                                      \
        mv a0, TESTNUM;                                                        \
        j _eoc;                                                                \
1:      li a0, -1;                                                             \
        j _eoc;

//-----------------------------------------------------------------------
// Data Section Macro
//-----------------------------------------------------------------------

#define EXTRA_DATA

#define RVTEST_DATA_BEGIN                                                      \
        EXTRA_DATA                                                             \
        .align 4;                                                              \
        .global begin_signature;                                               \
begin_signature:

#define RVTEST_DATA_END                                                        \
        .align 4;                                                              \
        .global end_signature;                                                 \
end_signature:

// clang-format on

#endif
