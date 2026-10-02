// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Author: Marco Bertuletti

#if (NUM_CORES == 16)
#define BEAM (4)
#define EMBED (16)
#define TDSAMPLES (16)
#endif

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

// Convolution weights. With REPLICATE_F, l2_F and l1_F hold one copy of the
// weights per RedMulE, in slots of an odd multiple of one tile, so that the
// RedMulEs running in lockstep read their copies from different banks.

#define F_WIDTH (EMBED * 3 * EMBED * CONV1D_WF)
#define F_TILE (NUM_BANKS_PER_TILE * sizeof(int32_t) / sizeof(int16_t))
#if defined(REPLICATE_F) && defined(PIPELINED)
#define F_STRIDE ((((F_WIDTH + F_TILE - 1) / F_TILE) | 1) * F_TILE)
#define F_COPIES (NUM_REDMULE_TILES > 0 ? NUM_REDMULE_TILES : 1)
#else
#define F_STRIDE (0)
#define F_COPIES (1)
#endif
#define F_SIZE (F_COPIES * (F_STRIDE > 0 ? F_STRIDE : F_WIDTH))

// Bytes to transfer for n weights, including all the copies
#define F_BYTES(n) (((F_COPIES - 1) * F_STRIDE + (n)) * sizeof(int16_t))

// Layout of the attention operands. With TILESHIFT, the per-batch slots of
// Q, Kt, V, A, As and Aw are rounded up to an odd multiple of one tile, so
// the batches processed concurrently by the RedMulEs start in different
// tiles. On top of that, the three operands of each attention GEMM start in
// different sub-groups: Q, Aw at +0, Kt, V at +1 and As, A at +2 sub-groups
// from a NUM_BANKS-aligned base. Without TILESHIFT, slots are dense.

#define TS_TILE (NUM_BANKS_PER_TILE * sizeof(int32_t) / sizeof(int16_t))
#define TS_ALIGN (NUM_BANKS * sizeof(int32_t) / sizeof(int16_t))
#define TS_MAX(a, b) (((a) > (b)) ? (a) : (b))
#ifdef TILESHIFT
#define TS_SUB_GROUP                                                           \
  (NUM_BANKS_PER_SUB_GROUP * sizeof(int32_t) / sizeof(int16_t))
#define TS_SLOT(n) (((((n) + TS_TILE - 1) / TS_TILE) | 1) * TS_TILE)
#define TS_ROUND(n) ((((n) + TS_ALIGN - 1) / TS_ALIGN) * TS_ALIGN)
#else
#define TS_SUB_GROUP (0)
#define TS_SLOT(n) (n)
#define TS_ROUND(n) (n)
#endif

// Offsets of Kt and V in l1_act (Q is at 0) for nb batches of slot elements,
// and offset of the attention scores and output in l1_scratch
#define TS_KT_OFFSET(nb, slot) (TS_ROUND((nb) * (slot)) + TS_SUB_GROUP)
#define TS_V_OFFSET(nb, slot)                                                  \
  (TS_ROUND(TS_KT_OFFSET(nb, slot) + (nb) * (slot)) + TS_SUB_GROUP)
#define TS_A_OFFSET (2 * TS_SUB_GROUP)

// EBT: Batch = EMBED, tdEmbed = TDSAMPLES.
// TBE: Batch = TDSAMPLES, tdEmbed = EMBED. SeqLen = BEAM in both modes.
#define TS_EBT_SLOT TS_SLOT(BEAM * TDSAMPLES)
#define TS_TBE_SLOT TS_SLOT(BEAM * EMBED)
#define TS_SCORE_SLOT TS_SLOT(BEAM * BEAM)

#define ACT_SIZE (BEAM * EMBED * 3 * TDSAMPLES)
#define SCRATCH_SIZE (BEAM * (2 * EMBED) * TDSAMPLES * CONV1D_WF)
#define AW_SIZE (TS_MAX(EMBED, TDSAMPLES) * BEAM * BEAM)

#ifdef TILESHIFT
#define L1_ACT_SIZE                                                            \
  TS_MAX(ACT_SIZE,                                                             \
         TS_MAX(TS_V_OFFSET(EMBED, TS_EBT_SLOT) + EMBED * TS_EBT_SLOT,         \
                TS_V_OFFSET(TDSAMPLES, TS_TBE_SLOT) +                          \
                    TDSAMPLES * TS_TBE_SLOT))
#define L1_SCRATCH_SIZE                                                        \
  TS_MAX(SCRATCH_SIZE,                                                         \
         TS_A_OFFSET + TS_MAX(EMBED, TDSAMPLES) *                              \
                           TS_MAX(TS_SCORE_SLOT,                               \
                                  TS_MAX(TS_EBT_SLOT, TS_TBE_SLOT)))
#define L1_AW_SIZE                                                             \
  TS_MAX(AW_SIZE, TS_MAX(EMBED, TDSAMPLES) * TS_SCORE_SLOT)
#else
#define L1_ACT_SIZE (ACT_SIZE)
#define L1_SCRATCH_SIZE (SCRATCH_SIZE)
#define L1_AW_SIZE (AW_SIZE)
#endif

// Size of the input and output of each layer, [BEAM][EMBED][TDSAMPLES]
#define X_SIZE (BEAM * EMBED * TDSAMPLES)

// - l1_act:     dense activations: layernorm output, attention operands Q, Kt
//               and V, permuted attention output, pipelined FFN output.
// - l1_scratch: im2col buffer of the convolutions, attention scores and
//               attention output.
// - l1_F:       convolution weights.
// - l1_arena:   three views of the same memory, x, y and aw, used at
//               different times, so the arena is only as large as its
//               largest view. In every layer:
//                 x      holds the layer input until the layernorm read it,
//                 y      holds the output of a convolution (QKV projection,
//                        FFN up-projection, layer output), overwriting x,
//                 aw     holds the softmax output, overwriting the QKV
//                        projection after the permutation read it.
//               The output of a layer left in y is therefore already the
//               input x of the next layer.

__fp16 l2_I[X_SIZE] __attribute__((aligned(sizeof(int32_t)), section(".l2")));
__fp16 l2_F[F_SIZE] __attribute__((aligned(sizeof(int32_t)), section(".l2")));

__fp16 l1_act[L1_ACT_SIZE]
  __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_scratch[L1_SCRATCH_SIZE]
  __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_F[F_SIZE]
  __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

typedef union {
  __fp16 x[X_SIZE];
  __fp16 y[BEAM * EMBED * 3 * TDSAMPLES];
  __fp16 aw[L1_AW_SIZE];
} l1_arena_t;

l1_arena_t l1_arena
  __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
