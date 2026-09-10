// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti

#ifndef BEAM
#define BEAM (32)
#endif

#ifndef EMBED
#define EMBED (32)
#endif

#ifndef TDSAMPLES
#define TDSAMPLES (32)
#endif

#define CONV1D_WF (3)

__fp16 l2_I[BEAM * EMBED * TDSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l2")));
__fp16 l2_F[EMBED * 3 * EMBED * CONV1D_WF]
    __attribute__((aligned(sizeof(int32_t)), section(".l2")));

// These should be allocated dinamically but we still do not have a malloc
// function that aligns data to the TCDM bounday without a shift from the
// canary. Therefore we allocate them statically.

__fp16 l1_T1[BEAM * EMBED * 3 * TDSAMPLES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
// Used for Im2col transformations.
__fp16 l1_T3[BEAM * (2 * EMBED) * TDSAMPLES * CONV1D_WF]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
// Convolution weights
__fp16 l1_F[EMBED * 3 * EMBED * CONV1D_WF]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

// l1_I, l1_T2 and l1_Aw are never live at the same time, in either attention()
// or ffn(), or across the two: l1_I is only read by the Layernorm stage that
// immediately follows its DMA load (dead once T1 holds the normed output),
// l1_T2 only holds data between the QKV/FFN-up Conv1D and the stage that
// consumes it (dead again before the next DMA-in or before attention_block()
// runs), and l1_Aw is touched only inside attention_block()'s softmax, by
// which point both l1_I and l1_T2 are already dead for that call -- ffn()
// never uses l1_Aw at all. Unioning them into one NUM_BANKS-aligned arena
// (sized to the largest member, l1_Aw) saves ~1MB of L1 vs three separate
// arrays, which is what let BEAM=128/EMBED=32/TDSAMPLES=32 fit at all.
typedef union {
  __fp16 i[BEAM * EMBED * TDSAMPLES];
  __fp16 t2[BEAM * EMBED * 3 * TDSAMPLES];
  __fp16 aw[EMBED * BEAM * BEAM];
} l1_i_t2_aw_arena_t;

l1_i_t2_aw_arena_t l1_i_t2_aw_arena
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

#define l1_I (l1_i_t2_aw_arena.i)
#define l1_T2 (l1_i_t2_aw_arena.t2)
#define l1_Aw (l1_i_t2_aw_arena.aw)
