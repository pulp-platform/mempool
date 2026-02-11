// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti

#define NRX (32)
#define NF (32)
#define NS (32)
#define DS (32)
#define DM (32)

#define D (DS + 2 + DM)
#define FD (DS + 2 + DM)
#define FK (3)

__fp16 l2_St1[NF * NS * D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l2_Wdw[FK * FK * D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l2_Wpw[FD * D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

// These should be allocated dinamically but we still do not have a malloc
// function that aligns data to the TCDM bounday without a shift from the
// canary. Therefore we allocate them statically.

__fp16 l1_St1[NF * NS * (DS + 2 + DM)]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_St2[NF * NS * (DS + 2 + DM)]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T1[NF * NS * (DS + 2 + DM)]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T2[NF * NS * (DS + 2 + DM)]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wdw[FK * FK * D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wpw[FD * D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
