// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Multi-cluster L1 transformer: two full transformer blocks
 * (attention + FFN, chained end-to-end with residual connections),
 * split across beam-parallel and attention-parallel clusters.
 *
 * Cluster roles (N_BEAM + N_ATTN active clusters, by default 4 + 1 = 5;
 * the remaining clusters of the mesh idle):
 *   - clusters 0..N_BEAM-1   ("beam clusters"): LayerNorm, Conv1D
 *     projections, residual adds, and the FFN (Conv1D -> GELU -> Conv1D),
 *     each parallel over a BEAM/N_BEAM-sized slice of beams.
 *   - clusters N_BEAM..N_BEAM+N_ATTN-1 ("attention clusters"): scaled
 *     dot-product attention.
 *
 * Between phases, data is redistributed cluster-to-cluster with plain
 * contiguous 1D DMA (never strided/2D -- a strided cross-cluster DMA was
 * found to lock up the NoC on this target; see l1_transformer_mc_min_f16
 * for the isolated repro). Each redistribution lands in a staging buffer
 * whose layout mirrors the transfer's natural contiguous shape; the actual
 * beam<->embed (or beam<->tdSamples) transpose is then done locally by
 * cores, the same technique used throughout for the K->Kt transpose.
 *
 * Block 1 attention ("EBT" in the single-cluster reference): attention
 * clusters each own a slice of EMBED (EC = EMBED/N_ATTN channels),
 * attending across the Beam axis with tdSamples as the per-token width.
 * Block 2 attention ("TBE"): attention clusters each own a slice of
 * TDSAMPLES (TC = TDSAMPLES/N_ATTN samples) instead, attending across the
 * Beam axis with Embed as the per-token width.
 *
 * PIPELINED: pipelined convolutions (im2col || RedMulE GEMM, GELU fused
 * into the FFN up-projection) and pipelined attention (Q x Kt of one round
 * of batches || softmax of the previous round), as in the single-cluster
 * l1_transformer_f16 app.
 *
 * Correctness checks: the QKV projection and output-projection filters are
 * identity-like pass-throughs (single non-zero center tap), so Q, K, V are
 * all exactly the LayerNorm output replicated, and the projection output
 * equals its input. This lets the projection + redistribution + transpose
 * logic be checked independently of the attention math itself, for both
 * blocks. The FFN/GELU stages are not independently numerically verified
 * here (would need a host-computed GELU reference) -- only structural
 * completion (DONE markers) is checked for those.
 */

#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_runtime.h"
#include <string.h>

#include "archi_redmule.h"
#include "baremetal/mempool_conv1d_f16.h"
#include "baremetal/mempool_gelu_f16.h"
#include "baremetal/mempool_layernorm_f16.h"
#include "baremetal/mempool_softmax_f16.h"
#include "hal_redmule.h"

#define BEAM (128)
#define EMBED (32)
#define TDSAMPLES (32)
#define WF (3)

#ifndef N_BEAM
#define N_BEAM (4) /* beam-parallel clusters (0..N_BEAM-1)  */
#endif
#ifndef N_ATTN
#define N_ATTN (1) /* embed/tdSamples-parallel clusters     */
#endif
#define BC (BEAM / N_BEAM)      /* beams handled by one beam cluster     */
#define EC (EMBED / N_ATTN)     /* embed channels per attn cluster (blk1)*/
#define TC (TDSAMPLES / N_ATTN) /* tdSamples per attn cluster (blk2)     */
#define ATTN0 (N_BEAM)          /* cluster id of first attention cluster */

#if N_BEAM + N_ATTN > ARCH_NUM_CLUSTER_X * ARCH_NUM_CLUSTER_Y
#error "N_BEAM + N_ATTN exceeds the number of clusters of the mesh"
#endif
#if (BEAM % N_BEAM) || (EMBED % N_ATTN) || (TDSAMPLES % N_ATTN)
#error "N_BEAM must divide BEAM, N_ATTN must divide EMBED and TDSAMPLES"
#endif

/* This target's libgcc predates soft-float f16<->f32 conversion helpers
 * (__truncsfhf2/__extendhfsf2), so any runtime float<->__fp16 cast, __fp16
 * comparison that the backend lowers via float promotion, or variadic
 * promotion of a __fp16 (e.g. passing one straight to printf) fails to
 * link. Stick to raw bit reinterpretation for all of that, and use a
 * host-precomputed LUT for the synthetic input pattern instead of casting
 * at runtime. */
static inline uint16_t fp16_bits(const __fp16 *x) {
  uint16_t u;
  memcpy(&u, x, sizeof(u));
  return u;
}
static inline void bits_fp16(uint16_t u, __fp16 *x) {
  memcpy(x, &u, sizeof(u));
}

/* IEEE-754 half-precision bits for 0.01 * (0..63), precomputed on the host. */
static const uint16_t INPUT_LUT[64] = {
    0x0000, 0x211f, 0x251f, 0x27ae, 0x291f, 0x2a66, 0x2bae, 0x2c7b,
    0x2d1f, 0x2dc3, 0x2e66, 0x2f0a, 0x2fae, 0x3029, 0x307b, 0x30cd,
    0x311f, 0x3171, 0x31c3, 0x3214, 0x3266, 0x32b8, 0x330a, 0x335c,
    0x33ae, 0x3400, 0x3429, 0x3452, 0x347b, 0x34a4, 0x34cd, 0x34f6,
    0x351f, 0x3548, 0x3571, 0x359a, 0x35c3, 0x35ec, 0x3614, 0x363d,
    0x3666, 0x368f, 0x36b8, 0x36e1, 0x370a, 0x3733, 0x375c, 0x3785,
    0x37ae, 0x37d7, 0x3800, 0x3814, 0x3829, 0x383d, 0x3852, 0x3866,
    0x387b, 0x388f, 0x38a4, 0x38b8, 0x38cd, 0x38e1, 0x38f6, 0x390a};
#define ONE_FP16_BITS (0x3c00) /* 1.0 in IEEE-754 half */

/**********************************************************************
 *  L1 arena: a physical cluster is EITHER a beam cluster OR an attention
 *  cluster (is_beam/is_attn are mutually exclusive), and within one
 *  cluster block 1's scratch is always fully dead (last read, with its
 *  closing mc_intra_cluster_sync()) before block 2 first touches the
 *  corresponding buffer -- res1's last read at Stage 14 precedes res2's
 *  first write at Stage 23, and every other block1/2 pair has an
 *  equally wide gap. But every binary is linked identically for every
 *  cluster, so without reuse the linker sums BEAM-side + ATTN-side +
 *  block1 + block2 buffers, all of which physically coexist in one
 *  cluster's L1 only in the worst case, never in practice.
 *
 *  This union reclaims that: `beam` and `attn` overlap (one cluster only
 *  ever uses one), and within each side, `b1`/`a1` overlap with `b2`/`a2`.
 *  Every block1/block2 array pair has the SAME total byte count for any
 *  EMBED/TDSAMPLES/BEAM (it's the same BC*EMBED*TDSAMPLES tensor volume
 *  with axes reordered for attn_stage, or BEAM*EC*TDSAMPLES ==
 *  BEAM*EMBED*TDSAMPLES/N_ATTN == TC*BEAM*EMBED for the post-redistribute
 *  Q/Kt/V), so `union { b1_t b1; b2_t b2; }` never truncates either side.
 *  The beam-side qkv_t (block 2 only) and the S/Aw/A score matrices are
 *  where block1 and block2 sizes can legitimately differ (S/Aw/A match
 *  only when EC==TC, i.e. EMBED==TDSAMPLES) -- a plain C union already
 *  sizes itself to the larger member for that, no per-member padding
 *  needed.
 *
 *  Only l1_I, the filters, and the two block outputs must NOT be
 *  aliased: I is read as late as Stage 9, block1_out survives all the
 *  way from Stage 14 to Stage 23 while block 2's own scratch is reused
 *  underneath it, and block2_out is the final result.
 **********************************************************************/

/* ---- Block-local beam scratch: dead in full before the other block's
 * corresponding buffer is first touched, so block 1 and block 2 share one
 * copy. Field names drop the trailing 1/2 -- code below keeps using
 * l1_norm1/l1_norm2 etc. via the macros after this union. */
typedef struct {
  __fp16 norm[BC][EMBED][TDSAMPLES];
  __fp16 im2col_qkv[BC * EMBED * WF * TDSAMPLES];
  __fp16 qkv[BC][3 * EMBED][TDSAMPLES];
  __fp16 attn_stage[EMBED][BC][TDSAMPLES]; /* block1 order: [Embed][BC][Td] */
  __fp16 attn_out[BC][EMBED][TDSAMPLES];
  __fp16 im2col_out[BC * EMBED * WF * TDSAMPLES];
  __fp16 proj_out[BC][EMBED][TDSAMPLES];
  __fp16 res[BC][EMBED][TDSAMPLES];
  __fp16 norm_ffn[BC][EMBED][TDSAMPLES];
  __fp16 im2col_ffn_a[BC * EMBED * WF * TDSAMPLES];
  __fp16 ffn_hidden[BC][2 * EMBED][TDSAMPLES];
  __fp16 im2col_ffn_b[BC * (2 * EMBED) * WF * TDSAMPLES];
  __fp16 ffn_out[BC][EMBED][TDSAMPLES];
} l1_beam_scratch1_t;

typedef struct {
  __fp16 norm[BC][EMBED][TDSAMPLES];
  __fp16 im2col_qkv[BC * EMBED * WF * TDSAMPLES];
  __fp16 qkv[BC][3 * EMBED][TDSAMPLES];
  __fp16 qkv_t[BC][3][TDSAMPLES][EMBED];   /* t-major Q/K/V, sent per slice */
  __fp16 attn_stage[TDSAMPLES][BC][EMBED]; /* block2 order: [Td][BC][Embed] */
  __fp16 attn_out[BC][EMBED][TDSAMPLES];
  __fp16 im2col_out[BC * EMBED * WF * TDSAMPLES];
  __fp16 proj_out[BC][EMBED][TDSAMPLES];
  __fp16 res[BC][EMBED][TDSAMPLES];
  __fp16 norm_ffn[BC][EMBED][TDSAMPLES];
  __fp16 im2col_ffn_a[BC * EMBED * WF * TDSAMPLES];
  __fp16 ffn_hidden[BC][2 * EMBED][TDSAMPLES];
  __fp16 im2col_ffn_b[BC * (2 * EMBED) * WF * TDSAMPLES];
  __fp16 ffn_out[BC][EMBED][TDSAMPLES];
} l1_beam_scratch2_t;

typedef struct {
  __fp16 I[BC][EMBED][TDSAMPLES];
  __fp16 F1[3 * EMBED * EMBED * WF];       /* QKV proj, Embed->3*Embed */
  __fp16 F2[EMBED * EMBED * WF];           /* output proj, Embed->Embed */
  __fp16 F3[2 * EMBED * EMBED * WF];       /* FFN hidden, Embed->2*Embed */
  __fp16 F4[2 * EMBED * EMBED * WF];       /* FFN out, 2*Embed->Embed */
  __fp16 block1_out[BC][EMBED][TDSAMPLES]; /* ffn_out1 + res1 */
  __fp16 block2_out[BC][EMBED][TDSAMPLES]; /* ffn_out2 + res2 (FINAL) */
  union {
    l1_beam_scratch1_t b1;
    l1_beam_scratch2_t b2;
  } scratch;
} l1_beam_t;

/* ---- Block-local attn scratch, partitioned by EC = EMBED/N_ATTN (block1)
 * or TC = TDSAMPLES/N_ATTN (block2, tdEmbed = EMBED). */
typedef struct {
  __fp16 Q_stage[BEAM][EC][TDSAMPLES];
  __fp16 K_stage[BEAM][EC][TDSAMPLES];
  __fp16 V_stage[BEAM][EC][TDSAMPLES];
  __fp16 Q[EC][BEAM][TDSAMPLES];
  __fp16 Kt[EC][BEAM][TDSAMPLES]; /* transposed K, the only form used */
  __fp16 V[EC][BEAM][TDSAMPLES];
  __fp16 S[EC][BEAM][BEAM];
  __fp16 Aw[EC][BEAM][BEAM];
  __fp16 A[EC][BEAM][TDSAMPLES];
} l1_attn_scratch1_t;

typedef struct {
  __fp16 Q_stage[BEAM][TC][EMBED]; /* this cluster's TC slice, t-major */
  __fp16 K_stage[BEAM][TC][EMBED];
  __fp16 V_stage[BEAM][TC][EMBED];
  __fp16 Q[TC][BEAM][EMBED];
  __fp16 Kt[TC][BEAM][EMBED];
  __fp16 V[TC][BEAM][EMBED];
  __fp16 S[TC][BEAM][BEAM];
  __fp16 Aw[TC][BEAM][BEAM];
  __fp16 A[TC][BEAM][EMBED];
} l1_attn_scratch2_t;

typedef union {
  l1_attn_scratch1_t a1;
  l1_attn_scratch2_t a2;
} l1_attn_t;

static union {
  l1_beam_t beam;
  l1_attn_t attn;
} l1_arena __attribute__((section(".l1"), aligned(64)));

/* Every stage below still reads/writes the original l1_* names. */
#define l1_I (l1_arena.beam.I)
#define l1_F1 (l1_arena.beam.F1)
#define l1_F2 (l1_arena.beam.F2)
#define l1_F3 (l1_arena.beam.F3)
#define l1_F4 (l1_arena.beam.F4)
#define l1_block1_out (l1_arena.beam.block1_out)
#define l1_block2_out (l1_arena.beam.block2_out)

#define l1_norm1 (l1_arena.beam.scratch.b1.norm)
#define l1_im2col_qkv1 (l1_arena.beam.scratch.b1.im2col_qkv)
#define l1_qkv1 (l1_arena.beam.scratch.b1.qkv)
#define l1_attn_stage1 (l1_arena.beam.scratch.b1.attn_stage)
#define l1_attn_out1 (l1_arena.beam.scratch.b1.attn_out)
#define l1_im2col_out1 (l1_arena.beam.scratch.b1.im2col_out)
#define l1_proj_out1 (l1_arena.beam.scratch.b1.proj_out)
#define l1_res1 (l1_arena.beam.scratch.b1.res)
#define l1_norm_ffn1 (l1_arena.beam.scratch.b1.norm_ffn)
#define l1_im2col_ffn1a (l1_arena.beam.scratch.b1.im2col_ffn_a)
#define l1_ffn_hidden1 (l1_arena.beam.scratch.b1.ffn_hidden)
#define l1_im2col_ffn1b (l1_arena.beam.scratch.b1.im2col_ffn_b)
#define l1_ffn_out1 (l1_arena.beam.scratch.b1.ffn_out)

#define l1_norm2 (l1_arena.beam.scratch.b2.norm)
#define l1_im2col_qkv2 (l1_arena.beam.scratch.b2.im2col_qkv)
#define l1_qkv2 (l1_arena.beam.scratch.b2.qkv)
#define l1_qkv2_t (l1_arena.beam.scratch.b2.qkv_t)
#define l1_attn_stage2 (l1_arena.beam.scratch.b2.attn_stage)
#define l1_attn_out2 (l1_arena.beam.scratch.b2.attn_out)
#define l1_im2col_out2 (l1_arena.beam.scratch.b2.im2col_out)
#define l1_proj_out2 (l1_arena.beam.scratch.b2.proj_out)
#define l1_res2 (l1_arena.beam.scratch.b2.res)
#define l1_norm_ffn2 (l1_arena.beam.scratch.b2.norm_ffn)
#define l1_im2col_ffn2a (l1_arena.beam.scratch.b2.im2col_ffn_a)
#define l1_ffn_hidden2 (l1_arena.beam.scratch.b2.ffn_hidden)
#define l1_im2col_ffn2b (l1_arena.beam.scratch.b2.im2col_ffn_b)
#define l1_ffn_out2 (l1_arena.beam.scratch.b2.ffn_out)

#define l1_Q1_stage (l1_arena.attn.a1.Q_stage)
#define l1_K1_stage (l1_arena.attn.a1.K_stage)
#define l1_V1_stage (l1_arena.attn.a1.V_stage)
#define l1_Q1 (l1_arena.attn.a1.Q)
#define l1_Kt1 (l1_arena.attn.a1.Kt)
#define l1_V1 (l1_arena.attn.a1.V)
#define l1_S1 (l1_arena.attn.a1.S)
#define l1_Aw1 (l1_arena.attn.a1.Aw)
#define l1_A1 (l1_arena.attn.a1.A)

#define l1_Q2_stage (l1_arena.attn.a2.Q_stage)
#define l1_K2_stage (l1_arena.attn.a2.K_stage)
#define l1_V2_stage (l1_arena.attn.a2.V_stage)
#define l1_Q2 (l1_arena.attn.a2.Q)
#define l1_Kt2 (l1_arena.attn.a2.Kt)
#define l1_V2 (l1_arena.attn.a2.V)
#define l1_S2 (l1_arena.attn.a2.S)
#define l1_Aw2 (l1_arena.attn.a2.Aw)
#define l1_A2 (l1_arena.attn.a2.A)

#define DONE(label)                                                            \
  do {                                                                         \
    if (core_id == 0 && cluster_id == 0) {                                     \
      printf("/* DONE: %s */\n", (label));                                     \
    }                                                                          \
    mc_global_barrier_xy();                                                    \
  } while (0)

#define NOINLINE __attribute__((noinline))

/* 1D DMAs with up to DMA_INFLIGHT transfers in flight. The DMA middle end
 * queues 8 transfers and the register front end does not stall on a full
 * queue, so wait for all of them every DMA_INFLIGHT launches; dma_flush()
 * waits for the rest. */
#define DMA_INFLIGHT (8)
static inline void dma_1d(uint32_t *n, uint64_t dst, uint64_t src,
                          size_t size) {
  mc_dma_async_1d(dst, src, size);
  if (++*n == DMA_INFLIGHT) {
    mc_dma_async_wait_all();
    *n = 0;
  }
}
static inline void dma_flush(void) { mc_dma_async_wait_all(); }

/* Elementwise residual add: dst = a + b, over BC*EMBED*TDSAMPLES elements,
 * parallelized across all cores of the (beam) cluster. Plain __fp16 `+`
 * gets lowered via float promotion on this target (missing libgcc
 * __extendhfsf2/__truncsfhf2, same pitfall noted at the top of this file),
 * so use the native vectorized fp16 add instruction directly, two
 * elements (one v2h) at a time -- BC*EMBED*TDSAMPLES is always even. */
static NOINLINE void residual_add(__fp16 *dst, const __fp16 *a, const __fp16 *b,
                                  uint32_t core_id, uint32_t num_cores) {
  for (uint32_t idx = 2 * core_id; idx < BC * EMBED * TDSAMPLES;
       idx += 2 * num_cores) {
    v2h va = *(v2h *)&a[idx];
    v2h vb = *(v2h *)&b[idx];
    v2h vy;
    asm volatile("vfadd.h %[vy], %[va], %[vb];"
                 : [vy] "=r"(vy)
                 : [va] "r"(va), [vb] "r"(vb));
    *(v2h *)&dst[idx] = vy;
  }
}

/* Softmax over nb BEAM x BEAM score matrices (contiguous in s / a). With
 * nb < num_cores, each matrix gets num_cores / nb cores, which split its
 * rows; otherwise each core takes whole matrices. */
static inline void softmax_batches(__fp16 *s, __fp16 *a, uint32_t nb,
                                   uint32_t core_id, uint32_t num_cores) {
  if (nb < num_cores) {
    uint32_t cores_per_batch = num_cores / nb;
    uint32_t idx = core_id / cores_per_batch;
    if (idx < nb) {
      softmax_parallel_2x4_f16vec(&s[idx * BEAM * BEAM], &a[idx * BEAM * BEAM],
                                  BEAM, BEAM, core_id % cores_per_batch,
                                  cores_per_batch);
    }
  } else {
    for (uint32_t i = core_id; i < nb; i += num_cores) {
      softmax_parallel_2x4_f16vec(&s[i * BEAM * BEAM], &a[i * BEAM * BEAM],
                                  BEAM, BEAM, 0, 1);
    }
  }
}

/* Conv1D of the BC beams of this cluster. With PIPELINED, im2col and the
 * RedMulE GEMMs overlap and post (or NULL) is applied in place on the
 * output; otherwise post must be NULL. */
static inline void conv(__fp16 const *in, __fp16 const *f, __fp16 *out,
                        __fp16 *cols, uint32_t ci, uint32_t co,
                        conv1d_post_t post, uint32_t core_id,
                        uint32_t num_cores) {
#ifdef PIPELINED
  conv1d_pipelined_f16(in, f, 0, out, cols, BC, ci, co, TDSAMPLES, WF, post,
                       core_id, num_cores);
#else
  (void)post;
  conv1d_f16(in, f, out, cols, BC, ci, co, TDSAMPLES, WF, 1, core_id,
             num_cores);
#endif
}

/* S = Q x Kt and Aw = softmax(S) for nb batches with td-wide tokens. With
 * PIPELINED, in round r the RedMulEs compute Q x Kt of batches
 * [r*R, (r+1)*R) while all cores compute the softmax of the batches of
 * round r-1 (one benchmark region). Otherwise, Q x Kt then softmax (two
 * regions). */
static NOINLINE void attn_scores(__fp16 *Q, __fp16 *Kt, __fp16 *S, __fp16 *Aw,
                                 uint32_t nb, uint32_t td, uint32_t core_id,
                                 uint32_t num_cores) {
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

#ifdef PIPELINED
  mempool_start_benchmark();
  for (uint32_t bb = 0; bb < nb + num_redmules; bb += num_redmules) {
    uint32_t ii = bb + redmule_id;
    uint32_t launched = (redmule_id < num_redmules) && (ii < nb);
    if (launched) {
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg((unsigned int)&Q[ii * BEAM * td],
                  (unsigned int)&Kt[ii * BEAM * td],
                  (unsigned int)&S[ii * BEAM * BEAM], (uint16_t)BEAM,
                  (uint16_t)td, (uint16_t)BEAM, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
    }
    if (bb > 0) {
      uint32_t prev = bb - num_redmules;
      uint32_t n = (nb - prev < num_redmules) ? (nb - prev) : num_redmules;
      softmax_batches(&S[prev * BEAM * BEAM], &Aw[prev * BEAM * BEAM], n,
                      core_id, num_cores);
    }
    /* The wake-up is latched if the job already finished */
    if (launched) {
      mempool_wfi();
    }
    mc_intra_cluster_sync();
  }
  mempool_stop_benchmark();
#else
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < nb; i += num_redmules) {
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg((unsigned int)&Q[i * BEAM * td],
                  (unsigned int)&Kt[i * BEAM * td],
                  (unsigned int)&S[i * BEAM * BEAM], (uint16_t)BEAM,
                  (uint16_t)td, (uint16_t)BEAM, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
      mempool_wfi();
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  mempool_start_benchmark();
  softmax_batches(S, Aw, nb, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
#endif
}

static NOINLINE void transpose_qkv1(uint32_t core_id, uint32_t num_cores) {
  /* Stage 4: locally transpose the beam-major staging buffers into the
   * embed-major Q/Kt/V layout. Both sides are contiguous in t here for a
   * fixed (ec, b) -- the same situation permute_qkv's Q/V (EBT) path
   * exploits in the single-cluster app -- so move two elements per v2h
   * instead of one __fp16 at a time. (Each core still writes one
   * contiguous TDSAMPLES-wide run per array, so this keeps the adjacent-
   * write property that avoided the RedMulE/im2col1d_f16 hang noted
   * below.) */
  mempool_start_benchmark();
  for (uint32_t idx = core_id; idx < EC * BEAM; idx += num_cores) {
    const uint32_t ec = idx / BEAM;
    const uint32_t b = idx % BEAM;
    uint32_t t = 0;
    if ((TDSAMPLES & 1u) == 0) {
      for (; t < TDSAMPLES; t += 2) {
        *(v2h *)&l1_Q1[ec][b][t] = *(v2h *)&l1_Q1_stage[b][ec][t];
        *(v2h *)&l1_Kt1[ec][b][t] = *(v2h *)&l1_K1_stage[b][ec][t];
        *(v2h *)&l1_V1[ec][b][t] = *(v2h *)&l1_V1_stage[b][ec][t];
      }
    } else {
      for (; t < TDSAMPLES; ++t) {
        l1_Q1[ec][b][t] = l1_Q1_stage[b][ec][t];
        l1_Kt1[ec][b][t] = l1_K1_stage[b][ec][t];
        l1_V1[ec][b][t] = l1_V1_stage[b][ec][t];
      }
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void transpose_attn_out2(uint32_t core_id, uint32_t num_cores) {
  /* Stage 21: locally transpose the tdSamples-major staging buffer into
   * the beam-major layout the output Conv1D needs. Left scalar
   * deliberately: l1_attn_stage2 has t as its OUTERMOST axis, so varying
   * t here strides by BC*EMBED on the source side -- the same TBE
   * situation the single-cluster permute_result leaves unvectorized. */
  mempool_start_benchmark();
  for (uint32_t idx = core_id; idx < EMBED * BC; idx += num_cores) {
    const uint32_t e = idx / BC;
    const uint32_t b = idx % BC;
    for (uint32_t t = 0; t < TDSAMPLES; ++t) {
      l1_attn_out2[b][e][t] = l1_attn_stage2[t][b][e];
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void reorder_qkv2(uint32_t core_id, uint32_t num_cores) {
  /* Stage 18: reorder the received [BEAM][TC][EMBED] slices into
   * Q2/Kt2/V2[TC][BEAM][EMBED]. Both sides are contiguous along e, so move
   * two elements per v2h. */
  mempool_start_benchmark();
  for (uint32_t idx = core_id; idx < TC * BEAM; idx += num_cores) {
    const uint32_t tc = idx / BEAM;
    const uint32_t b = idx % BEAM;
    if ((EMBED & 1u) == 0) {
      for (uint32_t e = 0; e < EMBED; e += 2) {
        *(v2h *)&l1_Q2[tc][b][e] = *(v2h *)&l1_Q2_stage[b][tc][e];
        *(v2h *)&l1_Kt2[tc][b][e] = *(v2h *)&l1_K2_stage[b][tc][e];
        *(v2h *)&l1_V2[tc][b][e] = *(v2h *)&l1_V2_stage[b][tc][e];
      }
    } else {
      for (uint32_t e = 0; e < EMBED; ++e) {
        l1_Q2[tc][b][e] = l1_Q2_stage[b][tc][e];
        l1_Kt2[tc][b][e] = l1_K2_stage[b][tc][e];
        l1_V2[tc][b][e] = l1_V2_stage[b][tc][e];
      }
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void transpose_qkv2(uint32_t core_id, uint32_t num_cores) {
  /* Stage 17a: transpose Q, K, V to t-major, so that the TC-wide slice of
   * t of each attention cluster is contiguous for every (beam, Q/K/V). */
  mempool_start_benchmark();
  for (uint32_t idx = core_id; idx < BC * 3 * TDSAMPLES; idx += num_cores) {
    const uint32_t b = idx / (3 * TDSAMPLES);
    const uint32_t k = (idx / TDSAMPLES) % 3;
    const uint32_t t = idx % TDSAMPLES;
    for (uint32_t e = 0; e < EMBED; ++e) {
      l1_qkv2_t[b][k][t][e] = l1_qkv2[b][k * EMBED + e][t];
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void beam_block1_ab(uint32_t core_id, uint32_t num_cores,
                                    uint32_t beam_offset) {
  /* Stage 1: LayerNorm */
  uint32_t num_cores_per_beam = num_cores / BC;
  uint32_t sub_id = core_id % num_cores_per_beam;
  uint32_t b_ln = core_id / num_cores_per_beam;

  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&l1_I[b_ln][0][0], &l1_norm1[b_ln][0][0], EMBED,
                                TDSAMPLES, sub_id, num_cores_per_beam);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 2: Conv1D QKV projection, Embed -> 3*Embed */
  mempool_start_benchmark();
  conv(&l1_norm1[0][0][0], l1_F1, &l1_qkv1[0][0][0], l1_im2col_qkv1, EMBED,
       3 * EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 3: redistribute Q, K, V to attention clusters (partitioned by
   * EC = EMBED/N_ATTN). Plain contiguous 1D DMA: for a fixed beam, the
   * EC channels belonging to one attention cluster's slice of Q/K/V are
   * already contiguous within l1_qkv1[b][*][*]. */
  mempool_start_benchmark();
  if (mc_is_dm_core()) {
    uint32_t n_dma = 0;
    const size_t chunk_bytes = EC * TDSAMPLES * sizeof(uint16_t);
    for (uint32_t a = 0; a < N_ATTN; ++a) {
      const uint32_t dst_cluster = ATTN0 + a;
      for (uint32_t b = 0; b < BC; ++b) {
        const uint32_t global_beam = beam_offset + b;

        uint32_t q_off = (uint32_t)((uintptr_t)&l1_Q1_stage[global_beam][0][0] -
                                    (uintptr_t)local(0));
        dma_1d(&n_dma, (uint64_t)remote_cid(dst_cluster, q_off),
               (uint64_t)(uintptr_t)&l1_qkv1[b][a * EC][0], chunk_bytes);

        uint32_t k_off = (uint32_t)((uintptr_t)&l1_K1_stage[global_beam][0][0] -
                                    (uintptr_t)local(0));
        dma_1d(&n_dma, (uint64_t)remote_cid(dst_cluster, k_off),
               (uint64_t)(uintptr_t)&l1_qkv1[b][EMBED + a * EC][0],
               chunk_bytes);

        uint32_t v_off = (uint32_t)((uintptr_t)&l1_V1_stage[global_beam][0][0] -
                                    (uintptr_t)local(0));
        dma_1d(&n_dma, (uint64_t)remote_cid(dst_cluster, v_off),
               (uint64_t)(uintptr_t)&l1_qkv1[b][2 * EMBED + a * EC][0],
               chunk_bytes);
      }
    }
    dma_flush();
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void attn_block1(uint32_t core_id, uint32_t num_cores,
                                 uint32_t embed_offset) {
  transpose_qkv1(core_id, num_cores);

  /* Stages 5a, 5b: scores Q x Kt and softmax, batched over EC channels. */
  attn_scores(&l1_Q1[0][0][0], &l1_Kt1[0][0][0], &l1_S1[0][0][0],
              &l1_Aw1[0][0][0], EC, TDSAMPLES, core_id, num_cores);
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  /* Stage 5c: Aw x V matmul. */
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < EC; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(&l1_Aw1[i][0][0]);
      unsigned int W_ptr = (unsigned int)(&l1_V1[i][0][0]);
      unsigned int O_ptr = (unsigned int)(&l1_A1[i][0][0]);
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(I_ptr, W_ptr, O_ptr, (uint16_t)BEAM, (uint16_t)BEAM,
                  (uint16_t)TDSAMPLES, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
      mempool_wfi();
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 6: redistribute attention output back to beam clusters. For a
   * fixed embed channel, the BC beams of one beam cluster are already
   * contiguous within l1_A1[ec][*][*]. */
  mempool_start_benchmark();
  if (mc_is_dm_core()) {
    uint32_t n_dma = 0;
    const size_t chunk_bytes = BC * TDSAMPLES * sizeof(uint16_t);
    for (uint32_t c = 0; c < N_BEAM; ++c) {
      for (uint32_t ec_local = 0; ec_local < EC; ++ec_local) {
        const uint32_t ec_global = embed_offset + ec_local;
        uint32_t dst_off =
            (uint32_t)((uintptr_t)&l1_attn_stage1[ec_global][0][0] -
                       (uintptr_t)local(0));
        dma_1d(&n_dma, (uint64_t)remote_cid(c, dst_off),
               (uint64_t)(uintptr_t)&l1_A1[ec_local][c * BC][0], chunk_bytes);
      }
    }
    dma_flush();
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void beam_block1_c_block2_a(uint32_t core_id,
                                            uint32_t num_cores,
                                            uint32_t beam_offset) {
  uint32_t num_cores_per_beam = num_cores / BC;
  uint32_t sub_id = core_id % num_cores_per_beam;
  uint32_t b_ln = core_id / num_cores_per_beam;

  /* Stage 7: locally transpose the embed-major staging buffer into the
   * beam-major layout the output Conv1D needs. Both l1_attn_out1 and
   * l1_attn_stage1 are contiguous in t for a fixed (b, e) -- same as
   * Stage 4 and the single-cluster permute_result's EBT path -- so use
   * v2h here too. */
  mempool_start_benchmark();
  for (uint32_t idx = core_id; idx < EMBED * BC; idx += num_cores) {
    const uint32_t e = idx / BC;
    const uint32_t b = idx % BC;
    if ((TDSAMPLES & 1u) == 0) {
      for (uint32_t t = 0; t < TDSAMPLES; t += 2) {
        *(v2h *)&l1_attn_out1[b][e][t] = *(v2h *)&l1_attn_stage1[e][b][t];
      }
    } else {
      for (uint32_t t = 0; t < TDSAMPLES; ++t) {
        l1_attn_out1[b][e][t] = l1_attn_stage1[e][b][t];
      }
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 8: output Conv1D, Embed -> Embed */
  mempool_start_benchmark();
  conv(&l1_attn_out1[0][0][0], l1_F2, &l1_proj_out1[0][0][0], l1_im2col_out1,
       EMBED, EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 9: residual, res1 = proj_out1 + I */
  mempool_start_benchmark();
  residual_add(&l1_res1[0][0][0], &l1_proj_out1[0][0][0], &l1_I[0][0][0],
               core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 10: LayerNorm (FFN) */
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&l1_res1[b_ln][0][0], &l1_norm_ffn1[b_ln][0][0],
                                EMBED, TDSAMPLES, sub_id, num_cores_per_beam);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 11: Conv1D, Embed -> 2*Embed */
  mempool_start_benchmark();
  conv(&l1_norm_ffn1[0][0][0], l1_F3, &l1_ffn_hidden1[0][0][0], l1_im2col_ffn1a,
       EMBED, 2 * EMBED,
#ifdef PIPELINED
       gelu_f16,
#else
       NULL,
#endif
       core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

#ifndef PIPELINED
  /* Stage 12: GELU, in-place, over the whole flat hidden buffer. */
  mempool_start_benchmark();
  gelu_f16(&l1_ffn_hidden1[0][0][0], BC * 2 * EMBED * TDSAMPLES, core_id,
           num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
#endif

  /* Stage 13: Conv1D, 2*Embed -> Embed */
  mempool_start_benchmark();
  conv(&l1_ffn_hidden1[0][0][0], l1_F4, &l1_ffn_out1[0][0][0], l1_im2col_ffn1b,
       2 * EMBED, EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 14: residual, block1_out = ffn_out1 + res1 */
  mempool_start_benchmark();
  residual_add(&l1_block1_out[0][0][0], &l1_ffn_out1[0][0][0],
               &l1_res1[0][0][0], core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 15: LayerNorm (block 2 attention input) */
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&l1_block1_out[b_ln][0][0],
                                &l1_norm2[b_ln][0][0], EMBED, TDSAMPLES, sub_id,
                                num_cores_per_beam);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 16: Conv1D QKV projection, Embed -> 3*Embed */
  mempool_start_benchmark();
  conv(&l1_norm2[0][0][0], l1_F1, &l1_qkv2[0][0][0], l1_im2col_qkv2, EMBED,
       3 * EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  transpose_qkv2(core_id, num_cores);

  /* Stage 17: redistribute Q, K, V to attention clusters, partitioned by
   * TC = TDSAMPLES/N_ATTN: one contiguous [TC][EMBED] chunk per (attention
   * cluster, beam, Q/K/V). */
  mempool_start_benchmark();
  if (mc_is_dm_core()) {
    uint32_t n_dma = 0;
    const size_t chunk_bytes2 = TC * EMBED * sizeof(uint16_t);
    for (uint32_t a = 0; a < N_ATTN; ++a) {
      const uint32_t dst_cluster = ATTN0 + a;
      for (uint32_t b = 0; b < BC; ++b) {
        const uint32_t global_beam = beam_offset + b;
        __fp16 *dst[3] = {&l1_Q2_stage[global_beam][0][0],
                          &l1_K2_stage[global_beam][0][0],
                          &l1_V2_stage[global_beam][0][0]};
        for (uint32_t k = 0; k < 3; ++k) {
          uint32_t off = (uint32_t)((uintptr_t)dst[k] - (uintptr_t)local(0));
          dma_1d(&n_dma, (uint64_t)remote_cid(dst_cluster, off),
                 (uint64_t)(uintptr_t)&l1_qkv2_t[b][k][a * TC][0],
                 chunk_bytes2);
        }
      }
    }
    dma_flush();
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void attn_block2(uint32_t core_id, uint32_t num_cores,
                                 uint32_t t_offset) {
  reorder_qkv2(core_id, num_cores);

  /* Stages 19a, 19b: scores Q x Kt and softmax, batched over TC samples. */
  attn_scores(&l1_Q2[0][0][0], &l1_Kt2[0][0][0], &l1_S2[0][0][0],
              &l1_Aw2[0][0][0], TC, EMBED, core_id, num_cores);
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  /* Stage 19c: Aw x V matmul. */
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < TC; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(&l1_Aw2[i][0][0]);
      unsigned int W_ptr = (unsigned int)(&l1_V2[i][0][0]);
      unsigned int O_ptr = (unsigned int)(&l1_A2[i][0][0]);
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(I_ptr, W_ptr, O_ptr, (uint16_t)BEAM, (uint16_t)BEAM,
                  (uint16_t)EMBED, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
      mempool_wfi();
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 20: redistribute attention output back to beam clusters. For a
   * fixed tc, the BC beams of one beam cluster are already contiguous
   * within l1_A2[tc][*][*] (beam and embed are the innermost dims). */
  mempool_start_benchmark();
  if (mc_is_dm_core()) {
    uint32_t n_dma = 0;
    const size_t chunk_bytes3 = BC * EMBED * sizeof(uint16_t);
    for (uint32_t c = 0; c < N_BEAM; ++c) {
      for (uint32_t tc = 0; tc < TC; ++tc) {
        const uint32_t global_t = t_offset + tc;
        uint32_t dst_off =
            (uint32_t)((uintptr_t)&l1_attn_stage2[global_t][0][0] -
                       (uintptr_t)local(0));
        dma_1d(&n_dma, (uint64_t)remote_cid(c, dst_off),
               (uint64_t)(uintptr_t)&l1_A2[tc][c * BC][0], chunk_bytes3);
      }
    }
    dma_flush();
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

static NOINLINE void beam_block2_c(uint32_t core_id, uint32_t num_cores) {
  uint32_t num_cores_per_beam = num_cores / BC;
  uint32_t sub_id = core_id % num_cores_per_beam;
  uint32_t b_ln = core_id / num_cores_per_beam;

  transpose_attn_out2(core_id, num_cores);

  /* Stage 22: output Conv1D, Embed -> Embed */
  mempool_start_benchmark();
  conv(&l1_attn_out2[0][0][0], l1_F2, &l1_proj_out2[0][0][0], l1_im2col_out2,
       EMBED, EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 23: residual, res2 = proj_out2 + block1_out */
  mempool_start_benchmark();
  residual_add(&l1_res2[0][0][0], &l1_proj_out2[0][0][0],
               &l1_block1_out[0][0][0], core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 24: LayerNorm (FFN) */
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&l1_res2[b_ln][0][0], &l1_norm_ffn2[b_ln][0][0],
                                EMBED, TDSAMPLES, sub_id, num_cores_per_beam);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 25: Conv1D, Embed -> 2*Embed */
  mempool_start_benchmark();
  conv(&l1_norm_ffn2[0][0][0], l1_F3, &l1_ffn_hidden2[0][0][0], l1_im2col_ffn2a,
       EMBED, 2 * EMBED,
#ifdef PIPELINED
       gelu_f16,
#else
       NULL,
#endif
       core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

#ifndef PIPELINED
  /* Stage 26: GELU, in-place. */
  mempool_start_benchmark();
  gelu_f16(&l1_ffn_hidden2[0][0][0], BC * 2 * EMBED * TDSAMPLES, core_id,
           num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
#endif

  /* Stage 27: Conv1D, 2*Embed -> Embed */
  mempool_start_benchmark();
  conv(&l1_ffn_hidden2[0][0][0], l1_F4, &l1_ffn_out2[0][0][0], l1_im2col_ffn2b,
       2 * EMBED, EMBED, NULL, core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /* Stage 28: residual, block2_out = ffn_out2 + res2 (final output) */
  mempool_start_benchmark();
  residual_add(&l1_block2_out[0][0][0], &l1_ffn_out2[0][0][0],
               &l1_res2[0][0][0], core_id, num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

#ifdef VERIFY
/* Exchange check, run after the benchmark: both ends of each block 2
 * transfer hash what they hold, weighting each element by its position in
 * the global tensor. Per transfer, the hashes of the senders must add up to
 * those of the receivers (mod 2^32). */
static uint32_t verify_hash __attribute__((section(".l1")));

static inline uint32_t vh(const __fp16 *x, uint32_t pos) {
  return (uint32_t)fp16_bits(x) * (2 * pos + 1);
}

static uint32_t verify_out[2] __attribute__((section(".l1")));

static NOINLINE void verify_reduce(uint32_t slot, uint32_t h,
                                   uint32_t core_id) {
  __atomic_fetch_add(&verify_hash, h, __ATOMIC_RELAXED);
  mc_intra_cluster_sync();
  if (core_id == 0) {
    verify_out[slot] = verify_hash;
    verify_hash = 0;
  }
  mc_intra_cluster_sync();
}

static NOINLINE void verify(uint32_t is_beam, uint32_t is_attn,
                            uint32_t cluster_id, uint32_t core_id,
                            uint32_t num_cores) {
  uint32_t h = 0;
  if (core_id == 0) {
    verify_hash = 0;
  }
  mc_intra_cluster_sync();
  if (is_beam) {
    const uint32_t beam_offset = cluster_id * BC;
    /* Q/K/V of block 2, pos = ((b * 3 + k) * TDSAMPLES + t) * EMBED + e */
    for (uint32_t i = core_id; i < BC * 3 * EMBED * TDSAMPLES; i += num_cores) {
      const uint32_t b = i / (3 * EMBED * TDSAMPLES);
      const uint32_t ch = (i / TDSAMPLES) % (3 * EMBED);
      const uint32_t t = i % TDSAMPLES;
      const uint32_t k = ch / EMBED, e = ch % EMBED;
      h += vh(&l1_qkv2[b][ch][t],
              (((beam_offset + b) * 3 + k) * TDSAMPLES + t) * EMBED + e);
    }
    verify_reduce(0, h, core_id);
    /* Attention output of block 2, pos = (b * TDSAMPLES + t) * EMBED + e */
    h = 0;
    for (uint32_t i = core_id; i < TDSAMPLES * BC * EMBED; i += num_cores) {
      const uint32_t t = i / (BC * EMBED);
      const uint32_t b = (i / EMBED) % BC;
      const uint32_t e = i % EMBED;
      h += vh(&l1_attn_stage2[t][b][e],
              ((beam_offset + b) * TDSAMPLES + t) * EMBED + e);
    }
    verify_reduce(1, h, core_id);
  } else if (is_attn) {
    const uint32_t t_offset = (cluster_id - ATTN0) * TC;
    for (uint32_t i = core_id; i < TC * BEAM * EMBED; i += num_cores) {
      const uint32_t tc = i / (BEAM * EMBED);
      const uint32_t b = (i / EMBED) % BEAM;
      const uint32_t e = i % EMBED;
      const uint32_t t = t_offset + tc;
      h += vh(&l1_Q2[tc][b][e], ((b * 3 + 0) * TDSAMPLES + t) * EMBED + e);
      h += vh(&l1_Kt2[tc][b][e], ((b * 3 + 1) * TDSAMPLES + t) * EMBED + e);
      h += vh(&l1_V2[tc][b][e], ((b * 3 + 2) * TDSAMPLES + t) * EMBED + e);
    }
    verify_reduce(0, h, core_id);
    h = 0;
    for (uint32_t i = core_id; i < TC * BEAM * EMBED; i += num_cores) {
      const uint32_t tc = i / (BEAM * EMBED);
      const uint32_t b = (i / EMBED) % BEAM;
      const uint32_t e = i % EMBED;
      h += vh(&l1_A2[tc][b][e], (b * TDSAMPLES + t_offset + tc) * EMBED + e);
    }
    verify_reduce(1, h, core_id);
  }
  /* The clusters share one UART: print one cluster at a time */
  for (uint32_t c = 0; c < N_BEAM + N_ATTN; ++c) {
    if (cluster_id == c && core_id == 0) {
      printf("VERIFY cluster %d %s qkv2 %08x att2 %08x\n", cluster_id,
             is_beam ? "beam" : "attn", verify_out[0], verify_out[1]);
    }
    mc_global_barrier_xy();
  }
}
#endif

int main() {
  uint32_t eoc_val = 0;
  uint32_t core_id = mc_get_core_id();
  uint32_t cluster_id = mc_get_cluster_id();
  uint32_t num_cores = mempool_get_core_count();
  mc_barrier_xy_init();

  const uint32_t is_beam = (cluster_id < N_BEAM);
  const uint32_t is_attn =
      (cluster_id >= ATTN0) && (cluster_id < ATTN0 + N_ATTN);
  const uint32_t beam_offset = cluster_id * BC; /* beam clusters */
  const uint32_t attn_idx = cluster_id - ATTN0; /* attn clusters */
  const uint32_t embed_offset = attn_idx * EC;  /* block 1 */
  const uint32_t t_offset = attn_idx * TC;      /* block 2 */

  DONE("Start");

  /**********************************************************************
   *  Stage 0: synthesize deterministic input + filters (beam clusters)
   **********************************************************************/
  if (is_beam && mc_is_dm_core()) {
    for (uint32_t b = 0; b < BC; ++b) {
      for (uint32_t e = 0; e < EMBED; ++e) {
        for (uint32_t t = 0; t < TDSAMPLES; ++t) {
          uint32_t v = ((beam_offset + b) * EMBED + e) * TDSAMPLES + t;
          bits_fp16(INPUT_LUT[v % 64], &l1_I[b][e][t]);
        }
      }
    }
    /* Identity-like QKV projection filter: for output channel o, pick the
     * single input channel (o % EMBED) and pass it through unscaled on the
     * filter's center tap (k = WF/2); every other tap/channel is zero. */
    memset(l1_F1, 0, sizeof(l1_F1));
    for (uint32_t o = 0; o < 3 * EMBED; ++o) {
      uint32_t i = o % EMBED;
      bits_fp16(ONE_FP16_BITS, &l1_F1[(o * EMBED + i) * WF + (WF / 2)]);
    }
    /* Same idea for the output projection (Embed -> Embed). */
    memset(l1_F2, 0, sizeof(l1_F2));
    for (uint32_t o = 0; o < EMBED; ++o) {
      bits_fp16(ONE_FP16_BITS, &l1_F2[(o * EMBED + o) * WF + (WF / 2)]);
    }
    /* FFN hidden filter (Embed -> 2*Embed): same replication trick as the
     * QKV filter (each of the 2 copies passes the corresponding input
     * channel through unscaled). */
    memset(l1_F3, 0, sizeof(l1_F3));
    for (uint32_t o = 0; o < 2 * EMBED; ++o) {
      uint32_t i = o % EMBED;
      bits_fp16(ONE_FP16_BITS, &l1_F3[(o * EMBED + i) * WF + (WF / 2)]);
    }
    /* FFN out filter (2*Embed -> Embed): select only the FIRST Embed-wide
     * copy (channels 0..Embed-1 of the 2*Embed input), pass-through
     * unscaled; the second copy (channels Embed..2*Embed-1) is ignored
     * (all-zero weights). Since both copies carry identical GELU(input)
     * values, this makes the FFN-out result exactly GELU(ffn hidden
     * input) -- deterministic and checkable against a host-computed GELU
     * if desired, though this app does not do that numeric check itself. */
    memset(l1_F4, 0, sizeof(l1_F4));
    for (uint32_t o = 0; o < EMBED; ++o) {
      uint32_t i = o; /* first copy only */
      bits_fp16(ONE_FP16_BITS, &l1_F4[(o * (2 * EMBED) + i) * WF + (WF / 2)]);
    }
  }
  mc_global_barrier_xy();
  DONE("Generate inputs");

  /**********************************************************************
   *  Block 1, part A (beam clusters): LayerNorm -> QKV Conv1D ->
   *  redistribute Q,K,V to attention clusters.
   **********************************************************************/
  if (is_beam) {
    beam_block1_ab(core_id, num_cores, beam_offset);
  }
  mc_global_barrier_xy();
  DONE("Block 1: redistribute Q,K,V to attention clusters");

  /**********************************************************************
   *  Block 1, part B (attention clusters): local transpose -> attention.
   **********************************************************************/
  if (is_attn) {
    attn_block1(core_id, num_cores, embed_offset);
  }
  mc_global_barrier_xy();
  DONE("Block 1: attention output redistributed to beam clusters");

  /**********************************************************************
   *  Block 1, part C (beam clusters): local transpose -> output Conv1D ->
   *  residual -> FFN (LayerNorm -> Conv1D -> GELU -> Conv1D) -> residual
   *  -> Block 2, part A: LayerNorm -> QKV Conv1D -> redistribute.
   **********************************************************************/
  if (is_beam) {
    beam_block1_c_block2_a(core_id, num_cores, beam_offset);
  }
  mc_global_barrier_xy();
  DONE("Block 2: redistribute Q,K,V to attention clusters");

  /**********************************************************************
   *  Block 2, part B (attention clusters): local transpose -> attention,
   *  partitioned by TC = TDSAMPLES/N_ATTN with Embed as the per-token
   *  width.
   **********************************************************************/
  if (is_attn) {
    attn_block2(core_id, num_cores, t_offset);
  }
  mc_global_barrier_xy();
  DONE("Block 2: attention output redistributed to beam clusters");

  /**********************************************************************
   *  Block 2, part C (beam clusters): local transpose -> output Conv1D ->
   *  residual -> FFN (LayerNorm -> Conv1D -> GELU -> Conv1D) -> residual
   *  (final output).
   **********************************************************************/
  if (is_beam) {
    beam_block2_c(core_id, num_cores);
  }
  mc_global_barrier_xy();
  DONE("Block 2 complete");
#ifdef VERIFY
  verify(is_beam, is_attn, cluster_id, core_id, num_cores);
  mc_global_barrier_xy();
#endif

  mc_global_barrier_xy();
  mc_eoc(eoc_val);
  return 0;
}
