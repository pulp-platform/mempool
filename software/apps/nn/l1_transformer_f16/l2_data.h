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

// Size of the input and output of each layer, [BEAM][EMBED][TDSAMPLES]
#define X_SIZE (BEAM * EMBED * TDSAMPLES)
// Convolution weights, sized for the largest convolution (QKV projection)
#define F_SIZE (EMBED * 3 * EMBED * CONV1D_WF)

__fp16 l2_I[X_SIZE] __attribute__((aligned(sizeof(int32_t)), section(".l2")));
__fp16 l2_F[F_SIZE] __attribute__((aligned(sizeof(int32_t)), section(".l2")));

// Layout of the attention operands. With TILESHIFT, the per-batch slots of
// Q, Kt, V, A, As and Aw are rounded up to an odd multiple of one tile, so
// the batches processed concurrently by the RedMulEs start in different
// tiles. On top of that, the three operands of each attention GEMM start in
// different sub-groups: Q, Aw at +0, Kt, V at +1 and As, A at +2 sub-groups
// from a NUM_BANKS-aligned base. Without TILESHIFT, slots are dense.

#define EL_PER_WORD (sizeof(int32_t) / sizeof(int16_t))
#define TS_TILE (NUM_BANKS_PER_TILE * EL_PER_WORD)
#define TS_ALIGN (NUM_BANKS * EL_PER_WORD)

#define TS_MAX(a, b) (((a) > (b)) ? (a) : (b))
#ifdef TILESHIFT
#define TS_SUB_GROUP (NUM_BANKS_PER_SUB_GROUP * EL_PER_WORD)
#define TS_SLOT(n) (((((n) + TS_TILE - 1) / TS_TILE) | 1) * TS_TILE)
#define TS_ROUND(n) ((((n) + TS_ALIGN - 1) / TS_ALIGN) * TS_ALIGN)
#else
#define TS_SUB_GROUP (0)
#define TS_SLOT(n) (n)
#define TS_ROUND(n) (n)
#endif

// Offsets of Kt and V in l1.qkv (Q is at 0) for nb batches of slot elements,
// and offset of the attention scores and output in l1.im2col1
#define TS_KT_OFFSET(nb, slot) (TS_ROUND((nb) * (slot)) + TS_SUB_GROUP)
#define TS_V_OFFSET(nb, slot)                                                  \
  (TS_ROUND(TS_KT_OFFSET(nb, slot) + (nb) * (slot)) + TS_SUB_GROUP)
#define TS_A_OFFSET (2 * TS_SUB_GROUP)

// EBT: Batch = EMBED, tdEmbed = TDSAMPLES.
// TBE: Batch = TDSAMPLES, tdEmbed = EMBED. SeqLen = BEAM in both modes.
#define TS_EBT_SLOT TS_SLOT(BEAM *TDSAMPLES)
#define TS_TBE_SLOT TS_SLOT(BEAM *EMBED)
#define TS_SCORE_SLOT TS_SLOT(BEAM *BEAM)

#define QKV_SIZE (BEAM * EMBED * 3 * TDSAMPLES)
#define IM2COL_SIZE (BEAM * (2 * EMBED) * TDSAMPLES * CONV1D_WF)
#define AW_SIZE (TS_MAX(EMBED, TDSAMPLES) * BEAM * BEAM)

// Without TILESHIFT the slots are dense and the offsets are 0, so these reduce
// to the dense sizes, but the scores still need BEAM * BEAM per batch.
#define L1_QKV_SIZE                                                            \
  TS_MAX(                                                                      \
      QKV_SIZE,                                                                \
      TS_MAX(TS_V_OFFSET(EMBED, TS_EBT_SLOT) + EMBED * TS_EBT_SLOT,            \
             TS_V_OFFSET(TDSAMPLES, TS_TBE_SLOT) + TDSAMPLES * TS_TBE_SLOT))
#define L1_IM2COL1_SIZE                                                        \
  TS_MAX(IM2COL_SIZE,                                                          \
         TS_A_OFFSET +                                                         \
             TS_MAX(EMBED, TDSAMPLES) *                                        \
                 TS_MAX(TS_SCORE_SLOT, TS_MAX(TS_EBT_SLOT, TS_TBE_SLOT)))
#define L1_AW_SIZE TS_MAX(AW_SIZE, TS_MAX(EMBED, TDSAMPLES) * TS_SCORE_SLOT)

#ifdef FUSE_CHAIN
// Weights of the convolutions of a layer (QKV, output projection, FFN up,
// FFN down)
#define WEIGHT_SIZE (EMBED * EMBED * CONV1D_WF)
#define FC_QKV_SIZE (3 * WEIGHT_SIZE)
#define FC_OUT_SIZE (WEIGHT_SIZE)
#define FC_UP_SIZE (2 * WEIGHT_SIZE)
#define FC_DOWN_SIZE (2 * WEIGHT_SIZE)
#define FC_OUT (FC_QKV_SIZE)
#define FC_UP (FC_OUT + FC_OUT_SIZE)
#define FC_DOWN (FC_UP + FC_UP_SIZE)
#define L1_F_SIZE (FC_DOWN + FC_DOWN_SIZE)
#else
#define L1_F_SIZE (F_SIZE)
#endif

// L1 buffers of a layer. Each starts NUM_BANKS-aligned (TILESHIFT assumes
// it); the members of a union are used at different times.
//   x        layer input, then layer output (written by the output projection
//            or the FFN down-projection): the next layer finds it there.
//   proj     output of the convolutions that read x (QKV projection, FFN
//            up-projection and hidden). A pipelined convolution writes the
//            output of a chunk while it reads the input of the next one, so
//            proj follows x instead of overlapping it.
//   aw       softmax output, over x and proj once they are consumed.
//   im2col1  im2col of the convolutions, then the attention scores and the
//            attention output (at TS_A_OFFSET).
//   qkv      attention operands Q, Kt and V, in TILESHIFT slots.
//   im2col2  im2col of the output projection, over qkv once it is consumed
//            (in the chain, also of the FFN up-projection: consecutive stages
//            use different buffers). Without PIPELINED, the layernorm output
//            and the permuted attention output.
//   F        convolution weights.
// The order is the placement in L1.

#define L1_ALIGNED __attribute__((aligned(NUM_BANKS * sizeof(int32_t))))
typedef struct {
  union L1_ALIGNED {
    struct {
      __fp16 x[X_SIZE];
      __fp16 proj[3 * X_SIZE];
    };
    __fp16 aw[L1_AW_SIZE];
  };
  __fp16 im2col1[L1_IM2COL1_SIZE] L1_ALIGNED;
  union L1_ALIGNED {
    __fp16 qkv[L1_QKV_SIZE];
    __fp16 im2col2[L1_QKV_SIZE];
  };
  __fp16 F[L1_F_SIZE] L1_ALIGNED;
} l1_t;

l1_t l1 __attribute__((section(".l1_prio")));
