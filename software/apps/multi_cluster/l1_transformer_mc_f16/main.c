// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/*
 * Multi-cluster L1 transformer: the same four layers as the single-cluster
 * l1_transformer_f16 app (attention in the embed domain, FFN, attention in
 * the time domain, FFN), split over N_CLUSTERS clusters (default 2).
 *
 * - Layernorm, convolutions and FFN: each cluster owns BC = BEAM /
 *   N_CLUSTERS beams.
 * - Attention mixes all beams, so it is split along its batch dimension
 *   instead: each cluster owns NB = EMBED / N_CLUSTERS embedding channels
 *   (EBT) or TDSAMPLES / N_CLUSTERS time samples (TBE), over all BEAM beams.
 *   With fewer batches than RedMulEs, each batch is also split into slices
 *   of rows, so that every RedMulE gets a job.
 * - Between the two, Q, K, V and the attention output are exchanged with
 *   contiguous 1D DMA transfers: each cluster packs what every cluster
 *   needs into one contiguous block per destination, and the receiver
 *   unpacks it into its own layout (including the K -> Kt transpose).
 *
 * The same flags as the single-cluster app select the implementation:
 *   PIPELINED    pipelined convolutions (im2col || GEMM, Gelu fused) and
 *                pipelined Q*Kt || softmax
 *   TILESHIFT    attention operands in tile-shifted batch slots
 *   REPLICATE_F  one copy of each filter per RedMulE
 *
 * Clusters beyond N_CLUSTERS idle, but take part in the global barriers.
 * The input and the weights are synthesized at start (outside the
 * benchmarked regions) with the same generator and layout as the
 * verification build of the single-cluster app, so the two can be compared.
 * VERIFY prints per-cluster checksums; REDMULE_ZERO_OUTPUT (needed for that
 * comparison) zeroes every RedMulE output before the job, since RedMulE
 * accumulates into its output.
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

#ifndef BEAM
#define BEAM (128)
#endif
#ifndef EMBED
#define EMBED (32)
#endif
#ifndef TDSAMPLES
#define TDSAMPLES (32)
#endif
#define WF (3)

#ifndef N_CLUSTERS
#define N_CLUSTERS (2)
#endif
#if (BEAM % N_CLUSTERS) || (EMBED % N_CLUSTERS) || (TDSAMPLES % N_CLUSTERS)
#error "N_CLUSTERS must divide BEAM, EMBED and TDSAMPLES"
#endif
#if N_CLUSTERS > ARCH_NUM_CLUSTER_X * ARCH_NUM_CLUSTER_Y
#error "N_CLUSTERS exceeds the number of clusters of the mesh"
#endif
/* Smallest row slice of an attention batch given to one RedMulE */
#define MIN_SLICE_ROWS (32)
#define BC (BEAM / N_CLUSTERS) /* beams per cluster                  */
#define MAX2(a, b) (((a) > (b)) ? (a) : (b))
#define W_MAX MAX2(EMBED, TDSAMPLES) /* attention embedding width, max     */
#define NB_MAX (W_MAX / N_CLUSTERS)  /* attention batches per cluster, max */

typedef enum { EBT, TBE } attn_mode_t;

/**********************************************************************
 *  Attention layout (see l2_data.h of the single-cluster app). With
 *  TILESHIFT, batch slots are rounded up to an odd multiple of one tile,
 *  and q / kt,v / att start 0 / 1 / 2 sub-groups after an aligned base.
 **********************************************************************/

#define L1_ALIGN (NUM_BANKS * sizeof(int32_t))
#ifdef TILESHIFT
#define TS_TILE (NUM_BANKS_PER_TILE * sizeof(int32_t) / sizeof(int16_t))
#define TS_SUB_GROUP                                                           \
  (NUM_BANKS_PER_SUB_GROUP * sizeof(int32_t) / sizeof(int16_t))
#define TS_SLOT(n) (((((n) + TS_TILE - 1) / TS_TILE) | 1) * TS_TILE)
#else
#define TS_SUB_GROUP (0)
#define TS_SLOT(n) (n)
#endif
#define SLOT_Q_MAX TS_SLOT(BEAM *W_MAX) /* q, kt, v, attention output */
#define SLOT_S TS_SLOT(BEAM *BEAM)      /* scores, softmax output     */

/**********************************************************************
 *  Filters: QKV projection, output projection, FFN up and down. With
 *  REPLICATE_F each one is stored once per RedMulE, in slots of an odd
 *  multiple of one tile; RedMulE i reads copy i.
 **********************************************************************/

#define F_QKV_SIZE (3 * EMBED * EMBED * WF)
#define F_OUT_SIZE (EMBED * EMBED * WF)
#define F_UP_SIZE (2 * EMBED * EMBED * WF)
#define F_DOWN_SIZE (2 * EMBED * EMBED * WF)
#ifdef REPLICATE_F
#ifndef PIPELINED
#error "REPLICATE_F is only implemented for the PIPELINED convolutions"
#endif
#define F_TILE (NUM_BANKS_PER_TILE * sizeof(int32_t) / sizeof(int16_t))
#define F_SLOT(n) (((((n) + F_TILE - 1) / F_TILE) | 1) * F_TILE)
#define F_COPIES (NUM_REDMULE_TILES)
#else
#define F_SLOT(n) (n)
#define F_COPIES (1)
#endif

/**********************************************************************
 *  L1 buffers of one cluster
 *
 *  Persistent:
 *    l1_x      layer input and output, [BC][EMBED][TDSAMPLES]. Each layer
 *              reads it in its first layernorm and writes its output into
 *              it with its last convolution.
 *    l1_send   Q, K, V packed per destination cluster,
 *              [3][N_CLUSTERS][NB][BC][W]. Read by the DMA while the other
 *              cluster already writes its own receive buffers.
 *    l1_arecv  attention output received from each cluster,
 *              [N_CLUSTERS][NB][BC][W]. Written by the other cluster while
 *              this one still reads its attention buffers.
 *    l1_f_*    filters.
 *
 *  Phase buffers: the four phases of a layer never overlap in time, so
 *  they share one union. A phase is entered only after a global barrier
 *  when another cluster may write into it.
 **********************************************************************/

#define ALIGNED __attribute__((aligned(L1_ALIGN)))

typedef struct { /* attention, before the exchange of Q, K, V */
  __fp16 x_norm[BC * EMBED * TDSAMPLES] ALIGNED;
  __fp16 qkv[BC * 3 * EMBED * TDSAMPLES] ALIGNED;
  __fp16 cols[BC * EMBED * WF * TDSAMPLES] ALIGNED;
} pre_t;

typedef struct { /* attention core */
  __fp16 recv[3 * N_CLUSTERS * NB_MAX * BC * W_MAX] ALIGNED;
  __fp16 q[NB_MAX * SLOT_Q_MAX] ALIGNED;
  __fp16 kt[TS_SUB_GROUP + NB_MAX * SLOT_Q_MAX] ALIGNED;
  __fp16 v[TS_SUB_GROUP + NB_MAX * SLOT_Q_MAX] ALIGNED;
  __fp16 att[2 * TS_SUB_GROUP + NB_MAX * SLOT_S] ALIGNED;
  __fp16 probs[NB_MAX * SLOT_S] ALIGNED;
  __fp16 apack[N_CLUSTERS * NB_MAX * BC * W_MAX] ALIGNED;
} attn_t;

typedef struct { /* attention, after the exchange of the attention output */
  __fp16 att_p[BC * EMBED * TDSAMPLES] ALIGNED;
  __fp16 cols[BC * EMBED * WF * TDSAMPLES] ALIGNED;
} post_t;

typedef struct { /* feed-forward */
  __fp16 x_norm[BC * EMBED * TDSAMPLES] ALIGNED;
  __fp16 up[BC * 2 * EMBED * TDSAMPLES] ALIGNED;
  __fp16 cols[BC * 2 * EMBED * WF * TDSAMPLES] ALIGNED;
} ffn_t;

static union {
  pre_t pre;
  attn_t attn;
  post_t post;
  ffn_t ffn;
} l1_phase ALIGNED __attribute__((section(".l1")));

static __fp16 l1_x[BC * EMBED * TDSAMPLES] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_send[3 * N_CLUSTERS * NB_MAX * BC * W_MAX] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_arecv[N_CLUSTERS * NB_MAX * BC * W_MAX] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_f_qkv[F_COPIES * F_SLOT(F_QKV_SIZE)] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_f_out[F_COPIES * F_SLOT(F_OUT_SIZE)] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_f_up[F_COPIES * F_SLOT(F_UP_SIZE)] ALIGNED
    __attribute__((section(".l1")));
static __fp16 l1_f_down[F_COPIES * F_SLOT(F_DOWN_SIZE)] ALIGNED
    __attribute__((section(".l1")));

#ifdef REPLICATE_F
#define F_STRIDE(n) F_SLOT(n)
#else
#define F_STRIDE(n) (0)
#endif

/**********************************************************************
 *  Helpers
 *
 *  Each core has a STACK_SIZE (512 B) stack: the stages are kept in
 *  separate, non-inlined functions so that the deepest call chain (main ->
 *  layer -> stage -> kernel) fits in it.
 **********************************************************************/

#define NOINLINE __attribute__((noinline))

#ifdef VERIFY
/* Checksum of n halfwords, computed by core 0 of each active cluster and
 * recorded; chk_print prints them one cluster at a time, since the printf
 * output of concurrent clusters interleaves. */
#define CHK_MAX (384)
#define L1_LOCAL __attribute__((section(".l1"))) /* one copy per cluster */
static const char *chk_label[CHK_MAX] L1_LOCAL;
static uint32_t chk_idx[CHK_MAX] L1_LOCAL;
static uint32_t chk_hash[CHK_MAX] L1_LOCAL;
static uint32_t chk_count L1_LOCAL; /* .l1 is not zeroed: reset in main */
#define CHK_SAMPLES (16)
/* Batches per cluster whose Q*Kt, softmax and A*V are recomputed on core 0:
 * the reference uses soft-float, about 12M cycles per batch. */
#ifndef CHK_NUMERIC_BATCHES
#define CHK_NUMERIC_BATCHES (1)
#endif
static uint16_t chk_smp[CHK_MAX]
                       [CHK_SAMPLES] L1_LOCAL; /* evenly spaced values */

static NOINLINE void chk(const char *label, uint32_t idx, const __fp16 *buf,
                         uint32_t n, uint32_t core_id, uint32_t cluster_id) {
  (void)cluster_id;
  if (core_id == 0 && chk_count < CHK_MAX) {
    uint32_t h = 0;
    const uint16_t *q = (const uint16_t *)buf;
    for (uint32_t i = 0; i < n; i++) {
      h = h * 31 + q[i];
    }
    chk_label[chk_count] = label;
    chk_idx[chk_count] = idx;
    chk_hash[chk_count] = h;
    for (uint32_t i = 0; i < CHK_SAMPLES; i++) {
      chk_smp[chk_count][i] = q[i * (n / CHK_SAMPLES)];
    }
    chk_count++;
  }
  mc_intra_cluster_sync();
}

/* fp16 -> fp32 by bit manipulation (no libgcc helper for this target) */
static inline float h2f(const __fp16 *h) {
  uint16_t b = *(const uint16_t *)h;
  uint32_t sign = (uint32_t)(b >> 15) << 31, exp = (b >> 10) & 0x1f;
  uint32_t man = b & 0x3ff, f;
  if (exp == 0) {
    if (man == 0) {
      f = sign;
    } else { /* subnormal: normalize */
      exp = 127 - 15 + 1;
      while ((man & 0x400) == 0) {
        man <<= 1;
        exp--;
      }
      f = sign | (exp << 23) | ((man & 0x3ff) << 13);
    }
  } else if (exp == 0x1f) {
    f = sign | 0x7f800000 | (man << 13);
  } else {
    f = sign | ((exp - 15 + 127) << 23) | (man << 13);
  }
  union {
    uint32_t u;
    float f;
  } c = {f};
  return c.f;
}

/* Recomputes rows of A = P * V of one batch on core 0 and records the
 * number of outputs off by more than 1% of max(|ref|, 1e-2), and the
 * largest reference value (x1000). */
static NOINLINE void chk_av(const char *label, uint32_t idx, const __fp16 *P,
                            const __fp16 *V, const __fp16 *A, uint32_t S,
                            uint32_t W, uint32_t core_id) {
  if (core_id == 0 && chk_count < CHK_MAX) {
    static const uint32_t rows[4] = {0, 37, 64, 127};
    uint32_t bad = 0;
    float amax = 0.0f;
    for (uint32_t ri = 0; ri < 4; ri++) {
      uint32_t r = rows[ri] % S;
      for (uint32_t c = 0; c < W; c++) {
        float acc = 0.0f;
        for (uint32_t k = 0; k < S; k++) {
          acc += h2f(&P[r * S + k]) * h2f(&V[k * W + c]);
        }
        float got = h2f(&A[r * W + c]);
        float ref_abs = acc < 0 ? -acc : acc;
        float tol = 0.01f * (ref_abs > 0.01f ? ref_abs : 0.01f);
        float d = got - acc;
        if (d < 0)
          d = -d;
        if (d > tol)
          bad++;
        if (ref_abs > amax)
          amax = ref_abs;
      }
    }
    chk_label[chk_count] = label;
    chk_idx[chk_count] = idx;
    chk_hash[chk_count] = bad;
    for (uint32_t i = 0; i < CHK_SAMPLES; i++)
      chk_smp[chk_count][i] = 0;
    chk_smp[chk_count][0] =
        (uint16_t)(amax * 1000.0f > 65535.0f ? 65535 : amax * 1000.0f);
    chk_count++;
  }
  mc_intra_cluster_sync();
}

/* exp(x) for x <= 0 with fp32 multiplies only (newlib's expf is far too
 * slow on this core): 2^(x log2 e), polynomial for the fraction, about
 * 1e-6 relative error. */
static inline float exp_neg(float x) {
  if (x < -87.0f) {
    return 0.0f;
  }
  float t = x * 1.44269504f;
  int32_t i = (int32_t)t;
  if ((float)i > t) {
    i--;
  }
  float f = t - (float)i;
  float p =
      1.0f + f * (0.6931472f +
                  f * (0.2402265f +
                       f * (0.0555041f + f * (0.0096181f + f * 0.0013334f))));
  union {
    uint32_t u;
    float f;
  } c = {(uint32_t)(i + 127) << 23};
  return p * c.f;
}

/* Recomputes rows of P = softmax(Q * Kt) of one batch on core 0 (rows in
 * different slices) and records the number of outputs off by more than
 * 2e-3 + 2% of the reference, and the largest error (x1e4). */
static NOINLINE void chk_qk(const char *label, uint32_t idx, const __fp16 *Q,
                            const __fp16 *Kt, const __fp16 *P, uint32_t S,
                            uint32_t W, uint32_t core_id) {
  if (core_id == 0 && chk_count < CHK_MAX) {
    static const uint32_t rows[4] = {0, 37, 64, 127};
    static float sc[BEAM];
    uint32_t bad = 0;
    float emax = 0.0f;
    for (uint32_t ri = 0; ri < 4; ri++) {
      uint32_t r = rows[ri] % S;
      float m = -65504.0f, sum = 0.0f;
      for (uint32_t k = 0; k < S; k++) {
        float acc = 0.0f;
        for (uint32_t j = 0; j < W; j++) {
          acc += h2f(&Q[r * W + j]) * h2f(&Kt[j * S + k]);
        }
        sc[k] = acc;
        m = acc > m ? acc : m;
      }
      for (uint32_t k = 0; k < S; k++) {
        sc[k] = exp_neg(sc[k] - m);
        sum += sc[k];
      }
      for (uint32_t k = 0; k < S; k++) {
        float ref = sc[k] / sum;
        float d = h2f(&P[r * S + k]) - ref;
        if (d < 0)
          d = -d;
        if (d > 2e-3f + 0.02f * ref)
          bad++;
        if (d > emax)
          emax = d;
      }
    }
    chk_label[chk_count] = label;
    chk_idx[chk_count] = idx;
    chk_hash[chk_count] = bad;
    for (uint32_t i = 0; i < CHK_SAMPLES; i++)
      chk_smp[chk_count][i] = 0;
    chk_smp[chk_count][0] =
        (uint16_t)(emax * 1e4f > 65535.0f ? 65535 : emax * 1e4f);
    chk_count++;
  }
  mc_intra_cluster_sync();
}

/* Hash of the received attention output of global batch n, traversed in
 * the order of rows [self * BC, (self + 1) * BC) of A_n, to compare with
 * the hash of those rows recorded by the cluster that computed A_n. */
static NOINLINE void chk_attp(const char *label, uint32_t idx, uint32_t mode,
                              const __fp16 *att_p, uint32_t n, uint32_t W,
                              uint32_t core_id) {
  if (core_id == 0 && chk_count < CHK_MAX) {
    uint32_t h = 0;
    for (uint32_t b = 0; b < BC; b++) {
      for (uint32_t j = 0; j < W; j++) {
        uint32_t e = (mode == EBT) ? n : j, t = (mode == EBT) ? j : n;
        h = h * 31 + ((const uint16_t *)att_p)[(b * EMBED + e) * TDSAMPLES + t];
      }
    }
    chk_label[chk_count] = label;
    chk_idx[chk_count] = idx;
    chk_hash[chk_count] = h;
    for (uint32_t i = 0; i < CHK_SAMPLES; i++)
      chk_smp[chk_count][i] = 0;
    chk_count++;
  }
  mc_intra_cluster_sync();
}

static NOINLINE void chk_print(uint32_t core_id, uint32_t cluster_id) {
  for (uint32_t c = 0; c < N_CLUSTERS; c++) {
    if (cluster_id == c && core_id == 0) {
      for (uint32_t i = 0; i < chk_count; i++) {
        printf("CHK %s c%d %d %x\n", chk_label[i], c, chk_idx[i], chk_hash[i]);
        printf("SMP %s c%d %d", chk_label[i], c, chk_idx[i]);
        for (uint32_t j = 0; j < CHK_SAMPLES; j++) {
          printf(" %x", chk_smp[i][j]);
        }
        printf("\n");
      }
    }
    mc_global_barrier_xy();
  }
}
#endif

/* Address of a local L1 buffer as seen from cluster cid. */
static inline uint64_t at_cluster(uint32_t cid, uint32_t self, const void *p) {
  if (cid == self) {
    return (uint64_t)(uintptr_t)p;
  }
  return (uint64_t)remote_cid(cid, (uint32_t)((uintptr_t)p - local(0)));
}

static inline void copy_v2h(__fp16 *dst, const __fp16 *src, uint32_t n) {
  uint32_t i = 0;
  for (; i + 1 < n; i += 2) {
    *(v2h *)&dst[i] = *(v2h *)&src[i];
  }
  for (; i < n; i++) {
    dst[i] = src[i];
  }
}

#ifdef VERIFY
/* Synthesizes the input slice of this cluster and the weights with the
 * same generator and order as the single-cluster verification build. */
static NOINLINE void synthesize(uint32_t cluster_id) {
  uint32_t x = 12345;
  uint16_t *qi = (uint16_t *)l1_x;
  for (uint32_t i = 0; i < BEAM * EMBED * TDSAMPLES; i++) {
    x = x * 1103515245u + 12345u;
    uint16_t val =
        (uint16_t)(((x >> 31) << 15) | ((10 + ((x >> 12) & 3)) << 10) |
                   ((x >> 16) & 0x3ff));
    uint32_t b = i / (EMBED * TDSAMPLES);
    if (b / BC == cluster_id) {
      qi[i - cluster_id * BC * EMBED * TDSAMPLES] = val;
    }
  }
  /* One weight sequence; each filter is a prefix of it, as in the
   * single-cluster app where every layer loads a prefix of l2_F. */
  uint16_t *fq = (uint16_t *)l1_f_qkv, *fo = (uint16_t *)l1_f_out;
  uint16_t *fu = (uint16_t *)l1_f_up, *fd = (uint16_t *)l1_f_down;
  for (uint32_t i = 0; i < F_QKV_SIZE; i++) {
    x = x * 1103515245u + 12345u;
    uint16_t val =
        (uint16_t)(((x >> 31) << 15) | ((7 + ((x >> 12) & 3)) << 10) |
                   ((x >> 16) & 0x3ff));
    for (uint32_t c = 0; c < F_COPIES; c++) {
      fq[c * F_SLOT(F_QKV_SIZE) + i] = val;
      if (i < F_OUT_SIZE)
        fo[c * F_SLOT(F_OUT_SIZE) + i] = val;
      if (i < F_UP_SIZE)
        fu[c * F_SLOT(F_UP_SIZE) + i] = val;
      if (i < F_DOWN_SIZE)
        fd[c * F_SLOT(F_DOWN_SIZE) + i] = val;
    }
  }
}
#endif

/* Fast synthesis on all cores, for the timing builds: a fixed pattern of
 * small values with alternating signs. */
static NOINLINE void synthesize_fast(uint32_t core_id, uint32_t num_cores) {
  uint16_t *qi = (uint16_t *)l1_x;
  for (uint32_t i = core_id; i < BC * EMBED * TDSAMPLES; i += num_cores) {
    qi[i] = (uint16_t)(((i & 1) << 15) | 0x2c00 | ((i * 37) & 0x3ff));
  }
  uint16_t *f[4] = {(uint16_t *)l1_f_qkv, (uint16_t *)l1_f_out,
                    (uint16_t *)l1_f_up, (uint16_t *)l1_f_down};
  const uint32_t size[4] = {F_SLOT(F_QKV_SIZE), F_SLOT(F_OUT_SIZE),
                            F_SLOT(F_UP_SIZE), F_SLOT(F_DOWN_SIZE)};
  for (uint32_t k = 0; k < 4; k++) {
    for (uint32_t i = core_id; i < F_COPIES * size[k]; i += num_cores) {
      uint32_t w = i % size[k];
      f[k][i] = (uint16_t)(((w & 1) << 15) | 0x2000 | ((w * 13) & 0x3ff));
    }
  }
}

/* Layernorm of the BC beams of x over EMBED, into x_norm. */
static NOINLINE void layernorm(const __fp16 *x, __fp16 *x_norm,
                               uint32_t core_id, uint32_t num_cores) {
  uint32_t num_cores_per_beam = num_cores / BC;
  uint32_t sub_id = core_id % num_cores_per_beam;
  uint32_t b = core_id / num_cores_per_beam;
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&x[b * EMBED * TDSAMPLES],
                                &x_norm[b * EMBED * TDSAMPLES], EMBED,
                                TDSAMPLES, sub_id, num_cores_per_beam);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/* Convolution of the BC beams, with an optional in-place post-operation. */
static NOINLINE void conv(const __fp16 *in, __fp16 *f, uint32_t f_stride,
                          __fp16 *out, __fp16 *cols, uint32_t ci, uint32_t co,
                          conv1d_post_t post, uint32_t core_id,
                          uint32_t num_cores) {
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(in, f, f_stride, out, cols, BC, ci, co, TDSAMPLES, WF,
                       post, core_id, num_cores);
#else
  (void)f_stride;
  conv1d_f16(in, f, out, cols, BC, ci, co, TDSAMPLES, WF, 1, core_id,
             num_cores);
  if (post) {
    post(out, BC * co * TDSAMPLES, core_id, num_cores);
  }
  mc_intra_cluster_sync();
#endif
  mempool_stop_benchmark();
}

/**********************************************************************
 *  Attention block on the NB batches of this cluster (see the
 *  single-cluster attention_block): A = softmax(Q * Kt) * V, with the
 *  scores in A and the softmax output in probs.
 *
 *  The RedMulE jobs are slices of rows of a batch: with fewer batches than
 *  RedMulEs, each batch is split into up to SeqLen / MIN_SLICE_ROWS slices
 *  so that every RedMulE gets a job. Rows of Q * Kt, of the softmax and of
 *  A depend only on the same rows of Q, of the scores and of probs.
 **********************************************************************/

/* Slices per batch */
static inline uint32_t attn_slices(uint32_t Batch, uint32_t SeqLen,
                                   uint32_t num_redmules) {
  uint32_t slices = 1;
  while (Batch * slices * 2 <= num_redmules &&
         SeqLen / (slices * 2) >= MIN_SLICE_ROWS &&
         SeqLen % (slices * 2) == 0) {
    slices *= 2;
  }
  return slices;
}

/* Start one RedMulE GEMM job: O (rows x P) = I (rows x N) * W (N x P) */
static inline void redmule_start(const __fp16 *I, const __fp16 *W, __fp16 *O,
                                 uint32_t rows, uint32_t N, uint32_t P) {
#ifdef REDMULE_ZERO_OUTPUT
  for (uint32_t z = 0; z < rows * P; z++)
    ((uint16_t *)O)[z] = 0;
#endif
  hwpe_soft_clear();
  mempool_wait(10);
  redmule_cfg((unsigned int)I, (unsigned int)W, (unsigned int)O, (uint16_t)rows,
              (uint16_t)N, (uint16_t)P, 0, GEMM, Float16);
  mempool_wait(10);
  hwpe_trigger_job();
}

/* Softmax of jobs [first, first + n): num_cores / n cores per job */
static inline void softmax_jobs(__fp16 const *scores, __fp16 *probs,
                                uint32_t first, uint32_t n, uint32_t slices,
                                uint32_t rows, uint32_t SeqLen, uint32_t slot_s,
                                uint32_t core_id, uint32_t num_cores) {
  if (n < num_cores) {
    uint32_t cores_per_job = num_cores / n;
    uint32_t idx = core_id / cores_per_job;
    if (idx < n) {
      uint32_t jj = first + idx;
      uint32_t off = (jj / slices) * slot_s + (jj % slices) * rows * SeqLen;
      softmax_parallel_2x4_f16vec(&scores[off], &probs[off], rows, SeqLen,
                                  core_id % cores_per_job, cores_per_job);
    }
  } else {
    for (uint32_t jj = first + core_id; jj < first + n; jj += num_cores) {
      uint32_t off = (jj / slices) * slot_s + (jj % slices) * rows * SeqLen;
      softmax_parallel_2x4_f16vec(&scores[off], &probs[off], rows, SeqLen, 0,
                                  1);
    }
  }
}

static NOINLINE void attention_block(__fp16 const *Q, __fp16 const *Kt,
                                     __fp16 const *V, __fp16 *probs, __fp16 *A,
                                     uint32_t Batch, uint32_t SeqLen,
                                     uint32_t tdEmbed, uint32_t core_id,
                                     uint32_t num_cores) {
  __fp16 *scores = A;
  uint32_t slot_q = TS_SLOT(SeqLen * tdEmbed);
  uint32_t slot_s = TS_SLOT(SeqLen * SeqLen);
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  uint32_t slices = attn_slices(Batch, SeqLen, num_redmules);
  uint32_t rows = SeqLen / slices;
  uint32_t jobs = Batch * slices;

#ifdef PIPELINED
  // Round r: RedMulEs compute Q*Kt of jobs [r*R, (r+1)*R), all cores the
  // softmax of the jobs of round r-1.
  mempool_start_benchmark();
  for (uint32_t jb = 0; jb < jobs + num_redmules; jb += num_redmules) {
    uint32_t j = jb + redmule_id;
    uint32_t launched = (redmule_id < num_redmules) && (j < jobs);
    if (launched) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                    scores + b * slot_s + r0 * SeqLen, rows, tdEmbed, SeqLen);
    }
    if (jb > 0) {
      uint32_t prev = jb - num_redmules;
      uint32_t n = (jobs - prev < num_redmules) ? (jobs - prev) : num_redmules;
      softmax_jobs(scores, probs, prev, n, slices, rows, SeqLen, slot_s,
                   core_id, num_cores);
    }
    if (launched) {
      mempool_wfi();
    }
    mc_intra_cluster_sync();
  }
  mempool_stop_benchmark();
#else
  // Q*Kt
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(Q + b * slot_q + r0 * tdEmbed, Kt + b * slot_q,
                    scores + b * slot_s + r0 * SeqLen, rows, tdEmbed, SeqLen);
      mempool_wfi();
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  // Softmax
  mempool_start_benchmark();
  softmax_jobs(scores, probs, 0, jobs, slices, rows, SeqLen, slot_s, core_id,
               num_cores);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
#endif

  // A = Softmax(Q*Kt)*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t j = redmule_id; j < jobs; j += num_redmules) {
      uint32_t b = j / slices, r0 = (j % slices) * rows;
      redmule_start(probs + b * slot_s + r0 * SeqLen, V + b * slot_q,
                    A + b * slot_q + r0 * tdEmbed, rows, SeqLen, tdEmbed);
      mempool_wfi();
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/**********************************************************************
 *  Attention layer, x -> x. In mode EBT the attention batches are the
 *  embedding channels (width TDSAMPLES), in mode TBE the time samples
 *  (width EMBED). Batch n of the attention, element (b, j), is element
 *  (b, e, t) of the projections with (e, t) = (n, j) in EBT, (j, n) in TBE.
 *
 *  Data and buffers:
 *    x_norm   layernorm output                     pre.x_norm
 *    qkv      Q|K|V projection [BC][3*EMBED][T]    pre.qkv
 *    send     Q, K, V per destination cluster      l1_send
 *    recv     Q, K, V from every cluster           attn.recv
 *    q,kt,v   attention operands, NB batches       attn.q / kt / v
 *    probs    softmax output                       attn.probs
 *    att      scores, then attention output        attn.att
 *    apack    attention output per beam cluster    attn.apack
 *    arecv    attention output from every cluster  l1_arecv
 *    att_p    attention output [BC][EMBED][T]      post.att_p
 *    x        output                               l1_x
 **********************************************************************/

/* Shape of the attention in one mode */
typedef struct {
  uint32_t W;         /* attention width                         */
  uint32_t NB;        /* attention batches per cluster          */
  uint32_t SQ;        /* batch slot of q, kt, v, attention output */
  uint32_t block;     /* exchanged elements per cluster pair     */
  uint32_t part_size; /* elements of one of Q, K, V in send/recv */
} attn_shape_t;

static inline attn_shape_t attn_shape(attn_mode_t mode) {
  attn_shape_t a;
  a.W = (mode == TBE) ? EMBED : TDSAMPLES;
  a.NB = ((mode == TBE) ? TDSAMPLES : EMBED) / N_CLUSTERS;
  a.SQ = TS_SLOT(BEAM * a.W);
  a.block = a.NB * BC * a.W;
  a.part_size = N_CLUSTERS * a.block;
  return a;
}

#define ATT_Q (l1_phase.attn.q)
#define ATT_KT (&l1_phase.attn.kt[TS_SUB_GROUP])
#define ATT_V (&l1_phase.attn.v[TS_SUB_GROUP])
#define ATT_A (&l1_phase.attn.att[2 * TS_SUB_GROUP])

/* Layernorm, QKV projection, pack Q, K, V per destination cluster. */
static NOINLINE void attn_pre(attn_mode_t mode, uint32_t self, uint32_t core_id,
                              uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *qkv = l1_phase.pre.qkv;
  __fp16 *send = l1_send;
  (void)self;

  layernorm(l1_x, l1_phase.pre.x_norm, core_id, num_cores);
  conv(l1_phase.pre.x_norm, l1_f_qkv, F_STRIDE(F_QKV_SIZE), qkv,
       l1_phase.pre.cols, EMBED, 3 * EMBED, NULL, core_id, num_cores);
#ifdef VERIFY
  chk(mode == TBE ? "qkvTBE" : "qkvEBT", 0, qkv, BC * 3 * EMBED * TDSAMPLES,
      core_id, self);
#endif

  // send[part][d][n][b][j]: a row of W elements per (part, d, n, b)
  mempool_start_benchmark();
  if (mode == EBT) {
    for (uint32_t r = core_id; r < 3 * N_CLUSTERS * a.NB * BC; r += num_cores) {
      uint32_t b = r % BC, n = (r / BC) % a.NB;
      uint32_t d = (r / (BC * a.NB)) % N_CLUSTERS;
      uint32_t part = r / (BC * a.NB * N_CLUSTERS);
      uint32_t e = d * a.NB + n;
      copy_v2h(&send[r * a.W],
               &qkv[(b * 3 * EMBED + part * EMBED + e) * TDSAMPLES], a.W);
    }
  } else {
    for (uint32_t r = core_id; r < 3 * BC * EMBED; r += num_cores) {
      uint32_t e = r % EMBED, b = (r / EMBED) % BC, part = r / (EMBED * BC);
      const __fp16 *row = &qkv[(b * 3 * EMBED + part * EMBED + e) * TDSAMPLES];
      for (uint32_t t = 0; t < TDSAMPLES; t++) {
        uint32_t d = t / a.NB, n = t % a.NB;
        send[part * a.part_size + ((d * a.NB + n) * BC + b) * a.W + e] = row[t];
      }
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/* DMA of src blocks to every cluster: block d of each part goes to cluster
 * d, at the position of this cluster in dst. Up to DMA_INFLIGHT transfers
 * are in flight: the DMA middle end queues 8 transfers and the register
 * front end does not stall on a full queue. */
#define DMA_INFLIGHT (8)
static NOINLINE void exchange(__fp16 *dst, const __fp16 *src, uint32_t parts,
                              uint32_t part_size, uint32_t block, uint32_t self,
                              uint32_t core_id) {
  (void)core_id;
  mempool_start_benchmark();
  if (mc_is_dm_core()) {
    uint32_t n = 0;
    for (uint32_t part = 0; part < parts; part++) {
      for (uint32_t d = 0; d < N_CLUSTERS; d++) {
        mc_dma_async_1d(
            at_cluster(d, self, &dst[part * part_size + self * block]),
            (uint64_t)(uintptr_t)&src[part * part_size + d * block],
            block * sizeof(int16_t));
        if (++n == DMA_INFLIGHT) {
          mc_dma_async_wait_all();
          n = 0;
        }
      }
    }
    mc_dma_async_wait_all();
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/* Unpack Q, K, V: q[n][b][j], kt[n][j][b], v[n][b][j], b = s * BC + b_l. */
static NOINLINE void attn_unpack(attn_mode_t mode, uint32_t core_id,
                                 uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *recv = l1_phase.attn.recv;
  __fp16 *q = ATT_Q, *kt = ATT_KT, *v = ATT_V;

  mempool_start_benchmark();
  for (uint32_t r = core_id; r < N_CLUSTERS * a.NB * BC; r += num_cores) {
    uint32_t b_l = r % BC, n = (r / BC) % a.NB, s = r / (BC * a.NB);
    uint32_t b = s * BC + b_l;
    const __fp16 *rk = &recv[1 * a.part_size + r * a.W];
    copy_v2h(&q[n * a.SQ + b * a.W], &recv[0 * a.part_size + r * a.W], a.W);
    copy_v2h(&v[n * a.SQ + b * a.W], &recv[2 * a.part_size + r * a.W], a.W);
    for (uint32_t j = 0; j < a.W; j++) {
      kt[n * a.SQ + j * BEAM + b] = rk[j];
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/* Pack the attention output per beam cluster: apack[d][n][b_l][j]. */
static NOINLINE void attn_pack(attn_mode_t mode, uint32_t core_id,
                               uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *att = ATT_A;
  __fp16 *apack = l1_phase.attn.apack;

  mempool_start_benchmark();
  for (uint32_t r = core_id; r < N_CLUSTERS * a.NB * BC; r += num_cores) {
    uint32_t b_l = r % BC, n = (r / BC) % a.NB, d = r / (BC * a.NB);
    copy_v2h(&apack[r * a.W], &att[n * a.SQ + (d * BC + b_l) * a.W], a.W);
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
}

/* Unpack Q, K, V, attention, pack the output per beam cluster. */
static NOINLINE void attn_core(attn_mode_t mode, uint32_t self,
                               uint32_t core_id, uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  (void)self;

  attn_unpack(mode, core_id, num_cores);
#ifdef VERIFY
  for (uint32_t n = 0; n < a.NB; n++) {
    chk(mode == TBE ? "qTBE" : "qEBT", self * a.NB + n, &ATT_Q[n * a.SQ],
        BEAM * a.W, core_id, self);
  }
  for (uint32_t n = 0; n < a.NB; n++) {
    chk(mode == TBE ? "vTBE" : "vEBT", self * a.NB + n, &ATT_V[n * a.SQ],
        BEAM * a.W, core_id, self);
  }
#endif
  attention_block(ATT_Q, ATT_KT, ATT_V, l1_phase.attn.probs, ATT_A, a.NB, BEAM,
                  a.W, core_id, num_cores);
#ifdef VERIFY
  for (uint32_t n = 0; n < a.NB; n++) {
    chk(mode == TBE ? "pTBE" : "pEBT", self * a.NB + n,
        &l1_phase.attn.probs[n * SLOT_S], BEAM * BEAM, core_id, self);
    chk(mode == TBE ? "aTBE" : "aEBT", self * a.NB + n, &ATT_A[n * a.SQ],
        BEAM * a.W, core_id, self);
    for (uint32_t d = 0; d < N_CLUSTERS; d++) {
      chk(mode == TBE ? "axTBE" : "axEBT", (self * a.NB + n) * N_CLUSTERS + d,
          &ATT_A[n * a.SQ + d * BC * a.W], BC * a.W, core_id, self);
    }
    if (n < CHK_NUMERIC_BATCHES) {
      chk_qk(mode == TBE ? "qkTBE" : "qkEBT", self * a.NB + n, &ATT_Q[n * a.SQ],
             &ATT_KT[n * a.SQ], &l1_phase.attn.probs[n * SLOT_S], BEAM, a.W,
             core_id);
      chk_av(mode == TBE ? "avTBE" : "avEBT", self * a.NB + n,
             &l1_phase.attn.probs[n * SLOT_S], &ATT_V[n * a.SQ],
             &ATT_A[n * a.SQ], BEAM, a.W, core_id);
    }
  }
#endif
  attn_pack(mode, core_id, num_cores);
}

/* Unpack the attention output, output projection into x. */
static NOINLINE void attn_post(attn_mode_t mode, uint32_t self,
                               uint32_t core_id, uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *arecv = l1_arecv;
  __fp16 *att_p = l1_phase.post.att_p;
  (void)self;

  // att_p[b_l][e][t] from arecv[s][n][b_l][j]
  mempool_start_benchmark();
  for (uint32_t r = core_id; r < N_CLUSTERS * a.NB * BC; r += num_cores) {
    uint32_t b_l = r % BC, n = (r / BC) % a.NB, s = r / (BC * a.NB);
    if (mode == EBT) {
      uint32_t e = s * a.NB + n;
      copy_v2h(&att_p[(b_l * EMBED + e) * TDSAMPLES], &arecv[r * a.W], a.W);
    } else {
      uint32_t t = s * a.NB + n;
      for (uint32_t e = 0; e < EMBED; e++) {
        att_p[(b_l * EMBED + e) * TDSAMPLES + t] = arecv[r * a.W + e];
      }
    }
  }
  mc_intra_cluster_sync();
  mempool_stop_benchmark();
#ifdef VERIFY
  for (uint32_t n = 0; n < N_CLUSTERS * a.NB; n++) {
    chk_attp(mode == TBE ? "axTBE" : "axEBT", n * N_CLUSTERS + self, mode,
             att_p, n, a.W, core_id);
  }
#endif

  conv(att_p, l1_f_out, F_STRIDE(F_OUT_SIZE), l1_x, l1_phase.post.cols, EMBED,
       EMBED, NULL, core_id, num_cores);
#ifdef VERIFY
  chk(mode == TBE ? "attnTBE" : "attnEBT", 0, l1_x, BC * EMBED * TDSAMPLES,
      core_id, self);
#endif
}

static NOINLINE void attention(attn_mode_t mode, uint32_t active, uint32_t self,
                               uint32_t core_id, uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);

  if (active)
    attn_pre(mode, self, core_id, num_cores);
  // Every cluster has packed (and is done with pre): recv may be written
  mc_global_barrier_xy();
  if (active)
    exchange(l1_phase.attn.recv, l1_send, 3, a.part_size, a.block, self,
             core_id);
  // Q, K, V of every cluster have arrived
  mc_global_barrier_xy();
  if (active)
    attn_core(mode, self, core_id, num_cores);
  // Every cluster has packed (arecv was last read in the previous layer)
  mc_global_barrier_xy();
  if (active)
    exchange(l1_arecv, l1_phase.attn.apack, 1, a.block, a.block, self, core_id);
  // The attention output of every cluster has arrived
  mc_global_barrier_xy();
  if (active)
    attn_post(mode, self, core_id, num_cores);
  mc_global_barrier_xy();
}

/**********************************************************************
 *  Feed-forward layer on the BC beams of this cluster, x -> x.
 *    x_norm   layernorm output                     ffn.x_norm
 *    up       up-projection, Gelu in place         ffn.up
 *    x        output                               l1_x
 **********************************************************************/

static NOINLINE void ffn(uint32_t active, uint32_t self, uint32_t core_id,
                         uint32_t num_cores) {
  __fp16 *x = l1_x;
  __fp16 *x_norm = l1_phase.ffn.x_norm;
  __fp16 *up = l1_phase.ffn.up;
  __fp16 *cols = l1_phase.ffn.cols;
  (void)self;

  if (active) {
    layernorm(x, x_norm, core_id, num_cores);
    conv(x_norm, l1_f_up, F_STRIDE(F_UP_SIZE), up, cols, EMBED, 2 * EMBED,
         gelu_f16, core_id, num_cores);
    conv(up, l1_f_down, F_STRIDE(F_DOWN_SIZE), x, cols, 2 * EMBED, EMBED, NULL,
         core_id, num_cores);
#ifdef VERIFY
    chk("ffn", 0, x, BC * EMBED * TDSAMPLES, core_id, self);
#endif
  }
  mc_global_barrier_xy();
}

int main() {
  uint32_t core_id = mc_get_core_id();
  uint32_t cluster_id = mc_get_cluster_id();
  uint32_t num_cores = mempool_get_core_count();
  mc_barrier_xy_init();

  const uint32_t active = (cluster_id < N_CLUSTERS);

#ifdef VERIFY
  if (active && core_id == 0) {
    chk_count = 0;
    synthesize(cluster_id);
  }
#else
  if (active) {
    synthesize_fast(core_id, num_cores);
    mc_intra_cluster_sync();
  }
#endif
  mc_global_barrier_xy();

  uint32_t t0 = mempool_get_timer();
  attention(EBT, active, cluster_id, core_id, num_cores);
  ffn(active, cluster_id, core_id, num_cores);
  attention(TBE, active, cluster_id, core_id, num_cores);
  ffn(active, cluster_id, core_id, num_cores);
  uint32_t t1 = mempool_get_timer();

  if (core_id == 0 && cluster_id == 0) {
    printf("TOTAL cycles %d\n", t1 - t0);
  }
  mc_global_barrier_xy();
#ifdef VERIFY
  chk_print(core_id, cluster_id);
#endif
  mc_eoc(0);
  return 0;
}
