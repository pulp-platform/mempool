// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti

#define BEAM (32)
#define EMBED (32)
#define TDSAMPLES (32)
#define CONV1D_WF (3)

__fp16 l2_I[BEAM * EMBED * TDSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l2")));
__fp16 l2_F[EMBED * 3 * EMBED * CONV1D_WF]
    __attribute__((aligned(sizeof(int32_t)), section(".l2")));
__fp16 l2_b[EMBED * 3]
    __attribute__((aligned(sizeof(int32_t)), section(".l2")));

// These should be allocated dinamically but we still do not have a malloc
// function that aligns data to the TCDM bounday without a shift from the
// canary. Therefore we allocate them statically.

__fp16 l1_I[BEAM * EMBED * TDSAMPLES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T1[BEAM * EMBED * 3 * TDSAMPLES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T2[BEAM * EMBED * 3 * TDSAMPLES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T3[BEAM * EMBED * CONV1D_WF * TDSAMPLES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_T4[EMBED * BEAM * BEAM]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_T5[EMBED * BEAM * BEAM]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_F[EMBED * 3 * EMBED * CONV1D_WF]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_b[EMBED * 3]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
