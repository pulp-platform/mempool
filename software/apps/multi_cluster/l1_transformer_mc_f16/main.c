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
 * comparison) zeroes every RedMulE output before the job.
 */

#include "mc_dma_pattern.h"
#include "mc_printf.h"
#include "mc_runtime.h"
#include <string.h>

#include "archi_redmule.h"
#include "baremetal/mempool_attention_f16.h"
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

#define MAX2(a, b) (((a) > (b)) ? (a) : (b))
#define BC (BEAM / N_CLUSTERS)       /* beams per cluster                  */
#define W_MAX MAX2(EMBED, TDSAMPLES) /* attention embedding width, max     */
#define NB_MAX (W_MAX / N_CLUSTERS)  /* attention batches per cluster, max */

typedef enum { EBT, TBE } attn_mode_t;
#define NOINLINE __attribute__((noinline))

#include "verify.h"

/**********************************************************************
 *  Attention layout (see l2_data.h of the single-cluster app). With
 *  TILESHIFT, batch slots are rounded up to an odd multiple of one tile,
 *  and q / kt,v / att start 0 / 1 / 2 sub-groups after an aligned base.
 **********************************************************************/

#define L1_ALIGN (NUM_BANKS * sizeof(int32_t))
#ifdef TILESHIFT

#define TS_TILE \
        (NUM_BANKS_PER_TILE * sizeof(int32_t) / sizeof(int16_t))
#define TS_SUB_GROUP \
        (NUM_BANKS_PER_SUB_GROUP * sizeof(int32_t) / sizeof(int16_t))
#define TS_SLOT(n) \
        (((((n) + TS_TILE - 1) / TS_TILE) | 1) * TS_TILE)

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

#define F_QKV_SIZE  (3 * EMBED * EMBED * WF)
#define F_OUT_SIZE  (EMBED * EMBED * WF)
#define F_UP_SIZE   (2 * EMBED * EMBED * WF)
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
#else
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
#endif

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

static inline void copy_v2h(__fp16 *dst, const __fp16 *src, uint32_t n) {
  uint32_t i = 0;
  for (; i + 1 < n; i += 2) {
    *(v2h *)&dst[i] = *(v2h *)&src[i];
  }
  for (; i < n; i++) {
    dst[i] = src[i];
  }
}

#define ATT_Q (l1_phase.attn.q)
#define ATT_KT (&l1_phase.attn.kt[TS_SUB_GROUP])
#define ATT_V (&l1_phase.attn.v[TS_SUB_GROUP])
#define ATT_A (&l1_phase.attn.att[2 * TS_SUB_GROUP])

/* Layernorm, QKV projection, pack Q, K, V per destination cluster. */
static NOINLINE void attn_pre(attn_mode_t mode, uint32_t self, uint32_t core_id,
                              uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *x = l1_x;
  __fp16 *x_norm = l1_phase.pre.x_norm;
  __fp16 *qkv = l1_phase.pre.qkv;
  __fp16 *cols = l1_phase.pre.cols;
  __fp16 *send = l1_send;
  (void)self;

  /**************************************************************************/
  /* Layernorm                                                              */
  /**************************************************************************/

  // Layer Normalization (over the raw EMBED-channel input)
  uint32_t num_cores_per_batch = num_cores / BC;
  uint32_t batch_id = core_id % num_cores_per_batch;
  uint32_t idx = core_id / num_cores_per_batch;

  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&x[idx * EMBED * TDSAMPLES],
                                &x_norm[idx * EMBED * TDSAMPLES], EMBED,
                                TDSAMPLES, batch_id, num_cores_per_batch);
  mc_intra_cluster_sync();
  mempool_stop_benchmark();

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: QKV projection (EMBED -> 3*EMBED)
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(x_norm, l1_f_qkv, F_STRIDE(F_QKV_SIZE), qkv, cols, BC,
                       EMBED, 3 * EMBED, TDSAMPLES, WF, NULL, core_id,
                       num_cores);
#else
  conv1d_f16(x_norm, l1_f_qkv, qkv, cols, BC, EMBED, 3 * EMBED, TDSAMPLES, WF,
             1, core_id, num_cores);
#endif
  mempool_stop_benchmark();

#ifdef VERIFY
  chk(mode == TBE ? "qkvTBE" : "qkvEBT", 0, qkv, BC * 3 * EMBED * TDSAMPLES,
      core_id, self);
#endif

  /**************************************************************************/
  /* Pack Q, K, V                                                           */
  /**************************************************************************/

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
        // Same buffer offset in the L1 of cluster d (local for d == self)
        uintptr_t to = (uintptr_t)&dst[part * part_size + self * block];
        uint64_t to_d =
            (d == self) ? (uint64_t)to : (uint64_t)remote_cid(d, to - local(0));
        mc_dma_async_1d(to_d,
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

  /**************************************************************************/
  /* Unpack Q, K, V                                                         */
  /**************************************************************************/

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

  /**************************************************************************/
  /* Attention                                                              */
  /**************************************************************************/

  attention_block_f16(ATT_Q, ATT_KT, ATT_V, l1_phase.attn.probs, ATT_A, a.NB,
                      BEAM, a.W, a.SQ, SLOT_S, core_id, num_cores);
                      
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

  /**************************************************************************/
  /* Pack result                                                            */
  /**************************************************************************/

  attn_pack(mode, core_id, num_cores);
}

/* Unpack the attention output, output projection into x. */
static NOINLINE void attn_post(attn_mode_t mode, uint32_t self,
                               uint32_t core_id, uint32_t num_cores) {
  attn_shape_t a = attn_shape(mode);
  __fp16 *arecv = l1_arecv;
  __fp16 *att_p = l1_phase.post.att_p;
  __fp16 *cols = l1_phase.post.cols;
  (void)self;

  /**************************************************************************/
  /* Unpack result                                                          */
  /**************************************************************************/

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

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: output projection (EMBED -> EMBED)
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(att_p, l1_f_out, F_STRIDE(F_OUT_SIZE), l1_x, cols, BC,
                       EMBED, EMBED, TDSAMPLES, WF, NULL, core_id, num_cores);
#else
  conv1d_f16(att_p, l1_f_out, l1_x, cols, BC, EMBED, EMBED, TDSAMPLES, WF, 1,
             core_id, num_cores);
#endif
  mempool_stop_benchmark();

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
    /************************************************************************/
    /* Layernorm                                                            */
    /************************************************************************/

    // Layer Normalization (over the raw EMBED-channel input)
    uint32_t num_cores_per_batch = num_cores / BC;
    uint32_t batch_id = core_id % num_cores_per_batch;
    uint32_t idx = core_id / num_cores_per_batch;

    mempool_start_benchmark();
    layernorm_parallel_2x4_f16vec(&x[idx * EMBED * TDSAMPLES],
                                  &x_norm[idx * EMBED * TDSAMPLES], EMBED,
                                  TDSAMPLES, batch_id, num_cores_per_batch);
    mc_intra_cluster_sync();
    mempool_stop_benchmark();

    /************************************************************************/
    /* Conv1D + Gelu                                                        */
    /************************************************************************/

    // Convolution: up-projection (EMBED -> 2*EMBED), Gelu applied in place
    mempool_start_benchmark();
#ifdef PIPELINED
    conv1d_pipelined_f16(x_norm, l1_f_up, F_STRIDE(F_UP_SIZE), up, cols, BC,
                         EMBED, 2 * EMBED, TDSAMPLES, WF, gelu_f16, core_id,
                         num_cores);
#else
    conv1d_f16(x_norm, l1_f_up, up, cols, BC, EMBED, 2 * EMBED, TDSAMPLES, WF,
               1, core_id, num_cores);
    gelu_f16(up, BC * 2 * EMBED * TDSAMPLES, core_id, num_cores);
    mc_intra_cluster_sync();
#endif
    mempool_stop_benchmark();

    /************************************************************************/
    /* Conv1D                                                               */
    /************************************************************************/

    // Convolution: down-projection (2*EMBED -> EMBED)
    mempool_start_benchmark();
#ifdef PIPELINED
    conv1d_pipelined_f16(up, l1_f_down, F_STRIDE(F_DOWN_SIZE), x, cols, BC,
                         2 * EMBED, EMBED, TDSAMPLES, WF, NULL, core_id,
                         num_cores);
#else
    conv1d_f16(up, l1_f_down, x, cols, BC, 2 * EMBED, EMBED, TDSAMPLES, WF, 1,
               core_id, num_cores);
#endif
    mempool_stop_benchmark();

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
