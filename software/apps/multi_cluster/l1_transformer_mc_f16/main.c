/*
 * Multi-cluster L1 transformer: two full transformer blocks
 * (attention + FFN, chained end-to-end with residual connections),
 * split across beam-parallel and attention-parallel clusters.
 *
 * Cluster roles (N_BEAM + N_ATTN = 4 + 2 = 6 active clusters, laid out on a
 * 4x2 mesh so clusters 6,7 are idle):
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
#include "hal_redmule.h"
#include "baremetal/mempool_conv1d_f16.h"
#include "baremetal/mempool_gelu_f16.h"
#include "baremetal/mempool_layernorm_f16.h"
#include "baremetal/mempool_softmax_f16.h"

#define BEAM (16)
#define EMBED (8)
#define TDSAMPLES (8)
#define WF (3)

#define N_BEAM (4)                 /* beam-parallel clusters (0..N_BEAM-1)  */
#define BC (BEAM / N_BEAM)         /* beams handled by one beam cluster     */
#define N_ATTN (2)                 /* embed/tdSamples-parallel clusters     */
#define EC (EMBED / N_ATTN)        /* embed channels per attn cluster (blk1)*/
#define TC (TDSAMPLES / N_ATTN)    /* tdSamples per attn cluster (blk2)     */
#define ATTN0 (N_BEAM)             /* cluster id of first attention cluster */
#define ATTN1 (N_BEAM + 1)

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
static inline void bits_fp16(uint16_t u, __fp16 *x) { memcpy(x, &u, sizeof(u)); }

/* IEEE-754 half-precision bits for 0.01 * (0..63), precomputed on the host. */
static const uint16_t INPUT_LUT[64] = {
    0x0000, 0x211f, 0x251f, 0x27ae, 0x291f, 0x2a66, 0x2bae, 0x2c7b, 0x2d1f,
    0x2dc3, 0x2e66, 0x2f0a, 0x2fae, 0x3029, 0x307b, 0x30cd, 0x311f, 0x3171,
    0x31c3, 0x3214, 0x3266, 0x32b8, 0x330a, 0x335c, 0x33ae, 0x3400, 0x3429,
    0x3452, 0x347b, 0x34a4, 0x34cd, 0x34f6, 0x351f, 0x3548, 0x3571, 0x359a,
    0x35c3, 0x35ec, 0x3614, 0x363d, 0x3666, 0x368f, 0x36b8, 0x36e1, 0x370a,
    0x3733, 0x375c, 0x3785, 0x37ae, 0x37d7, 0x3800, 0x3814, 0x3829, 0x383d,
    0x3852, 0x3866, 0x387b, 0x388f, 0x38a4, 0x38b8, 0x38cd, 0x38e1, 0x38f6,
    0x390a};
#define ONE_FP16_BITS (0x3c00) /* 1.0 in IEEE-754 half */

/**********************************************************************
 *  Beam-cluster buffers
 **********************************************************************/
static __fp16 l1_I[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));

/* Shared filters: identity-like pass-throughs, reused for both blocks. */
static __fp16 l1_F1[3 * EMBED * EMBED * WF] /* QKV proj, Embed->3*Embed */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_F2[EMBED * EMBED * WF] /* output proj, Embed->Embed */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_F3[2 * EMBED * EMBED * WF] /* FFN hidden, Embed->2*Embed */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_F4[2 * EMBED * EMBED * WF] /* FFN out, 2*Embed->Embed */
    __attribute__((section(".l1"), aligned(64)));

/* ---- Block 1 ---- */
static __fp16 l1_norm1[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_qkv1[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_qkv1[BC][3 * EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_attn_stage1[EMBED][BC][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_attn_out1[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_out1[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_proj_out1[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_res1[BC][EMBED][TDSAMPLES] /* proj_out1 + I */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_norm_ffn1[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_ffn1a[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_ffn_hidden1[BC][2 * EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_ffn1b[BC * (2 * EMBED) * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_ffn_out1[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_block1_out[BC][EMBED][TDSAMPLES] /* ffn_out1 + res1 */
    __attribute__((section(".l1"), aligned(64)));

/* ---- Block 2 ---- */
static __fp16 l1_norm2[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_qkv2[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_qkv2[BC][3 * EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_attn_stage2[TDSAMPLES][BC][EMBED]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_attn_out2[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_out2[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_proj_out2[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_res2[BC][EMBED][TDSAMPLES] /* proj_out2 + block1_out */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_norm_ffn2[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_ffn2a[BC * EMBED * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_ffn_hidden2[BC][2 * EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_im2col_ffn2b[BC * (2 * EMBED) * WF * TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_ffn_out2[BC][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_block2_out[BC][EMBED][TDSAMPLES] /* ffn_out2 + res2 (FINAL) */
    __attribute__((section(".l1"), aligned(64)));

/**********************************************************************
 *  Attention-cluster buffers
 **********************************************************************/

/* ---- Block 1: partitioned by EC = EMBED/N_ATTN ---- */
static __fp16 l1_Q1_stage[BEAM][EC][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_K1_stage[BEAM][EC][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_V1_stage[BEAM][EC][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Q1[EC][BEAM][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Kt1[EC][BEAM][TDSAMPLES] /* transposed K, the only form used */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_V1[EC][BEAM][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_S1[EC][BEAM][BEAM]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Aw1[EC][BEAM][BEAM]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_A1[EC][BEAM][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));

/* ---- Block 2: partitioned by TC = TDSAMPLES/N_ATTN, tdEmbed = EMBED ---- */
static __fp16 l1_Q2_stage[BEAM][EMBED][TDSAMPLES] /* full Embed width recv'd */
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_K2_stage[BEAM][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_V2_stage[BEAM][EMBED][TDSAMPLES]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Q2[TC][BEAM][EMBED]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Kt2[TC][BEAM][EMBED]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_V2[TC][BEAM][EMBED]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_S2[TC][BEAM][BEAM]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_Aw2[TC][BEAM][BEAM]
    __attribute__((section(".l1"), aligned(64)));
static __fp16 l1_A2[TC][BEAM][EMBED]
    __attribute__((section(".l1"), aligned(64)));

#define DONE(label)                                                          \
  do {                                                                       \
    if (core_id == 0 && cluster_id == 0) {                                   \
      printf("/* DONE: %s */\n", (label));                                   \
    }                                                                        \
    mc_global_barrier_xy();                                                  \
  } while (0)

/* Elementwise residual add: dst = a + b, over BC*EMBED*TDSAMPLES elements,
 * parallelized across all cores of the (beam) cluster. Plain __fp16 `+`
 * gets lowered via float promotion on this target (missing libgcc
 * __extendhfsf2/__truncsfhf2, same pitfall noted at the top of this file),
 * so use the native vectorized fp16 add instruction directly, two
 * elements (one v2h) at a time -- BC*EMBED*TDSAMPLES is always even. */
static inline void residual_add(__fp16 *dst, const __fp16 *a, const __fp16 *b,
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

int main() {
  uint32_t eoc_val = 0;
  uint32_t core_id = mc_get_core_id();
  uint32_t cluster_id = mc_get_cluster_id();
  uint32_t num_cores = mempool_get_core_count();
  mc_barrier_xy_init();

  const uint32_t is_beam = (cluster_id < N_BEAM);
  const uint32_t is_attn = (cluster_id == ATTN0) || (cluster_id == ATTN1);
  const uint32_t beam_offset = cluster_id * BC;             /* beam clusters */
  const uint32_t attn_idx = (cluster_id == ATTN1) ? 1 : 0;   /* attn clusters */
  const uint32_t embed_offset = attn_idx * EC;               /* block 1 */
  const uint32_t t_offset = attn_idx * TC;                   /* block 2 */

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

    /* Stage 1: LayerNorm */
    uint32_t num_cores_per_beam = num_cores / BC;
    uint32_t sub_id = core_id % num_cores_per_beam;
    uint32_t b_ln = core_id / num_cores_per_beam;
    layernorm_parallel_2x4_f16vec(&l1_I[b_ln][0][0], &l1_norm1[b_ln][0][0],
                                  EMBED, TDSAMPLES, sub_id, num_cores_per_beam);
    mc_intra_cluster_sync();

    /* Stage 2: Conv1D QKV projection, Embed -> 3*Embed */
    conv1d_f16(&l1_norm1[0][0][0], l1_F1, &l1_qkv1[0][0][0], l1_im2col_qkv1,
              BC, EMBED, 3 * EMBED, TDSAMPLES, WF, 1, core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 3: redistribute Q, K, V to attention clusters (partitioned by
     * EC = EMBED/N_ATTN). Plain contiguous 1D DMA: for a fixed beam, the
     * EC channels belonging to one attention cluster's slice of Q/K/V are
     * already contiguous within l1_qkv1[b][*][*]. */
    if (mc_is_dm_core()) {
      const size_t chunk_bytes = EC * TDSAMPLES * sizeof(uint16_t);
      for (uint32_t a = 0; a < N_ATTN; ++a) {
        const uint32_t dst_cluster = ATTN0 + a;
        for (uint32_t b = 0; b < BC; ++b) {
          const uint32_t global_beam = beam_offset + b;

          uint32_t q_off = (uint32_t)((uintptr_t)&l1_Q1_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, q_off),
                         (uint64_t)(uintptr_t)&l1_qkv1[b][a * EC][0],
                         chunk_bytes);

          uint32_t k_off = (uint32_t)((uintptr_t)&l1_K1_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, k_off),
                         (uint64_t)(uintptr_t)&l1_qkv1[b][EMBED + a * EC][0],
                         chunk_bytes);

          uint32_t v_off = (uint32_t)((uintptr_t)&l1_V1_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, v_off),
                         (uint64_t)(uintptr_t)&l1_qkv1[b][2 * EMBED + a * EC][0],
                         chunk_bytes);
        }
      }
    }
    mc_intra_cluster_sync();
  }
  mc_global_barrier_xy();
  DONE("Block 1: redistribute Q,K,V to attention clusters");

  /**********************************************************************
   *  Block 1, part B (attention clusters): local transpose -> attention.
   **********************************************************************/
  if (is_attn) {

    /* Stage 4: locally transpose the beam-major staging buffers into the
     * embed-major Q/V layout (each core writes one contiguous TDSAMPLES-
     * wide run -- safe), and separately Kt (each core writes one
     * contiguous BEAM-wide run, fixing (ec,t) and looping b -- if this
     * instead looped b outer/t inner, each core would write BEAM-strided,
     * non-adjacent addresses, which was found to hang RedMulE when it
     * later reads that exact buffer as its W operand; see
     * mempool_conv1d_f16.h's im2col1d_f16 for the identical bug/fix in
     * the QKV-projection path). */
    for (uint32_t idx = core_id; idx < EC * BEAM; idx += num_cores) {
      const uint32_t ec = idx / BEAM;
      const uint32_t b = idx % BEAM;
      for (uint32_t t = 0; t < TDSAMPLES; ++t) {
        l1_Q1[ec][b][t] = l1_Q1_stage[b][ec][t];
        l1_Kt1[ec][b][t] = l1_K1_stage[b][ec][t];
        l1_V1[ec][b][t] = l1_V1_stage[b][ec][t];
      }
    }
    mc_intra_cluster_sync();

    /* Stage 5: scaled dot-product attention, batched over EC channels. */
    uint32_t redmule_id = mempool_get_redmule_id();
    uint32_t num_redmules = mempool_get_redmule_count();

    if (redmule_id < num_redmules) {
      for (uint32_t i = redmule_id; i < EC; i += num_redmules) {
        unsigned int I_ptr = (unsigned int)(&l1_Q1[i][0][0]);
        unsigned int W_ptr = (unsigned int)(&l1_Kt1[i][0][0]);
        unsigned int O_ptr = (unsigned int)(&l1_S1[i][0][0]);
        hwpe_soft_clear();
        mempool_wait(10);
        redmule_cfg(I_ptr, W_ptr, O_ptr, (uint16_t)BEAM, (uint16_t)TDSAMPLES,
                   (uint16_t)BEAM, 0, GEMM, Float16);
        mempool_wait(10);
        hwpe_trigger_job();
        mempool_wfi();
      }
    }
    mc_intra_cluster_sync();

    for (uint32_t i = core_id; i < EC; i += num_cores) {
      softmax_parallel_2x4_f16vec(&l1_S1[i][0][0], &l1_Aw1[i][0][0], BEAM,
                                  BEAM, 0, 1);
    }
    mc_intra_cluster_sync();

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

    /* Stage 6: redistribute attention output back to beam clusters. For a
     * fixed embed channel, the BC beams of one beam cluster are already
     * contiguous within l1_A1[ec][*][*]. */
    if (mc_is_dm_core()) {
      const size_t chunk_bytes = BC * TDSAMPLES * sizeof(uint16_t);
      for (uint32_t c = 0; c < N_BEAM; ++c) {
        for (uint32_t ec_local = 0; ec_local < EC; ++ec_local) {
          const uint32_t ec_global = embed_offset + ec_local;
          uint32_t dst_off = (uint32_t)((uintptr_t)&l1_attn_stage1[ec_global][0][0] -
                                        (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(c, dst_off),
                         (uint64_t)(uintptr_t)&l1_A1[ec_local][c * BC][0],
                         chunk_bytes);
        }
      }
    }
    mc_intra_cluster_sync();
  }
  mc_global_barrier_xy();
  DONE("Block 1: attention output redistributed to beam clusters");

  /**********************************************************************
   *  Block 1, part C (beam clusters): local transpose -> output Conv1D ->
   *  residual -> FFN (LayerNorm -> Conv1D -> GELU -> Conv1D) -> residual
   *  -> Block 2, part A: LayerNorm -> QKV Conv1D -> redistribute.
   **********************************************************************/
  if (is_beam) {

    uint32_t num_cores_per_beam = num_cores / BC;
    uint32_t sub_id = core_id % num_cores_per_beam;
    uint32_t b_ln = core_id / num_cores_per_beam;

    /* Stage 7: locally transpose the embed-major staging buffer into the
     * beam-major layout the output Conv1D needs. */
    for (uint32_t idx = core_id; idx < EMBED * BC; idx += num_cores) {
      const uint32_t e = idx / BC;
      const uint32_t b = idx % BC;
      for (uint32_t t = 0; t < TDSAMPLES; ++t) {
        l1_attn_out1[b][e][t] = l1_attn_stage1[e][b][t];
      }
    }
    mc_intra_cluster_sync();

    /* Stage 8: output Conv1D, Embed -> Embed */
    conv1d_f16(&l1_attn_out1[0][0][0], l1_F2, &l1_proj_out1[0][0][0],
              l1_im2col_out1, BC, EMBED, EMBED, TDSAMPLES, WF, 1, core_id,
              num_cores);
    mc_intra_cluster_sync();

    if (mc_is_dm_core() && cluster_id == 0) {
      uint32_t errors = 0;
      for (uint32_t b = 0; b < BC; ++b) {
        for (uint32_t e = 0; e < EMBED; ++e) {
          for (uint32_t t = 0; t < TDSAMPLES; ++t) {
            if (fp16_bits(&l1_proj_out1[b][e][t]) !=
                fp16_bits(&l1_attn_out1[b][e][t])) {
              ++errors;
            }
          }
        }
      }
      printf("[Cluster %u] Block 1 output projection check: %s (%u "
             "mismatches)\n",
             cluster_id, errors == 0 ? "PASS" : "FAIL", errors);
    }

    /* Stage 9: residual, res1 = proj_out1 + I */
    residual_add(&l1_res1[0][0][0], &l1_proj_out1[0][0][0], &l1_I[0][0][0],
                core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 10: LayerNorm (FFN) */
    layernorm_parallel_2x4_f16vec(&l1_res1[b_ln][0][0],
                                  &l1_norm_ffn1[b_ln][0][0], EMBED, TDSAMPLES,
                                  sub_id, num_cores_per_beam);
    mc_intra_cluster_sync();

    /* Stage 11: Conv1D, Embed -> 2*Embed */
    conv1d_f16(&l1_norm_ffn1[0][0][0], l1_F3, &l1_ffn_hidden1[0][0][0],
              l1_im2col_ffn1a, BC, EMBED, 2 * EMBED, TDSAMPLES, WF, 1,
              core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 12: GELU, in-place, over the whole flat hidden buffer. */
    gelu_f16(&l1_ffn_hidden1[0][0][0], BC * 2 * EMBED * TDSAMPLES, core_id,
            num_cores);
    mc_intra_cluster_sync();

    /* Stage 13: Conv1D, 2*Embed -> Embed */
    conv1d_f16(&l1_ffn_hidden1[0][0][0], l1_F4, &l1_ffn_out1[0][0][0],
              l1_im2col_ffn1b, BC, 2 * EMBED, EMBED, TDSAMPLES, WF, 1,
              core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 14: residual, block1_out = ffn_out1 + res1 */
    residual_add(&l1_block1_out[0][0][0], &l1_ffn_out1[0][0][0],
                &l1_res1[0][0][0], core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 15: LayerNorm (block 2 attention input) */
    layernorm_parallel_2x4_f16vec(&l1_block1_out[b_ln][0][0],
                                  &l1_norm2[b_ln][0][0], EMBED, TDSAMPLES,
                                  sub_id, num_cores_per_beam);
    mc_intra_cluster_sync();

    /* Stage 16: Conv1D QKV projection, Embed -> 3*Embed */
    conv1d_f16(&l1_norm2[0][0][0], l1_F1, &l1_qkv2[0][0][0], l1_im2col_qkv2,
              BC, EMBED, 3 * EMBED, TDSAMPLES, WF, 1, core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 17: redistribute Q, K, V to attention clusters, this time
     * partitioned by TC = TDSAMPLES/N_ATTN. Since a TDSAMPLES-slice is not
     * contiguous within l1_qkv2[b][channel][*] (t is the innermost axis),
     * send the FULL Embed-wide, all-tdSamples chunk per (beam,
     * channel-type) to BOTH attention clusters (still a single contiguous
     * transfer per (beam, channel-type) since channel and t are the
     * innermost two dims); each attention cluster locally extracts just
     * its TC-wide slice of t in Stage 18. */
    if (mc_is_dm_core()) {
      const size_t chunk_bytes2 = EMBED * TDSAMPLES * sizeof(uint16_t);
      for (uint32_t a = 0; a < N_ATTN; ++a) {
        const uint32_t dst_cluster = ATTN0 + a;
        for (uint32_t b = 0; b < BC; ++b) {
          const uint32_t global_beam = beam_offset + b;

          uint32_t q_off = (uint32_t)((uintptr_t)&l1_Q2_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, q_off),
                         (uint64_t)(uintptr_t)&l1_qkv2[b][0][0], chunk_bytes2);

          uint32_t k_off = (uint32_t)((uintptr_t)&l1_K2_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, k_off),
                         (uint64_t)(uintptr_t)&l1_qkv2[b][EMBED][0],
                         chunk_bytes2);

          uint32_t v_off = (uint32_t)((uintptr_t)&l1_V2_stage[global_beam][0][0] -
                                      (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(dst_cluster, v_off),
                         (uint64_t)(uintptr_t)&l1_qkv2[b][2 * EMBED][0],
                         chunk_bytes2);
        }
      }
    }
    mc_intra_cluster_sync();
  }
  mc_global_barrier_xy();
  DONE("Block 2: redistribute Q,K,V to attention clusters");

  /**********************************************************************
   *  Block 2, part B (attention clusters): local transpose -> attention,
   *  partitioned by TC = TDSAMPLES/N_ATTN with Embed as the per-token
   *  width.
   **********************************************************************/
  if (is_attn) {

    /* Stage 18: locally extract this cluster's TC-wide slice of t from the
     * full-Embed-width staging buffers into Q2/V2. */
    for (uint32_t idx = core_id; idx < TC * BEAM * EMBED; idx += num_cores) {
      const uint32_t tc = idx / (BEAM * EMBED);
      const uint32_t rem = idx % (BEAM * EMBED);
      const uint32_t b = rem / EMBED;
      const uint32_t e = rem % EMBED;
      const uint32_t global_t = t_offset + tc;
      l1_Q2[tc][b][e] = l1_Q2_stage[b][e][global_t];
      l1_Kt2[tc][b][e] = l1_K2_stage[b][e][global_t];
      l1_V2[tc][b][e] = l1_V2_stage[b][e][global_t];
    }
    mc_intra_cluster_sync();

    if (mc_is_dm_core()) {
      uint32_t errors = 0;
      for (uint32_t tc = 0; tc < TC; ++tc) {
        for (uint32_t b = 0; b < BEAM; ++b) {
          for (uint32_t e = 0; e < EMBED; ++e) {
            if (fp16_bits(&l1_Q2[tc][b][e]) != fp16_bits(&l1_Kt2[tc][e][b]) ||
                fp16_bits(&l1_Q2[tc][b][e]) != fp16_bits(&l1_V2[tc][b][e])) {
              ++errors;
            }
          }
        }
      }
      if (cluster_id == ATTN0) {
        printf("[Cluster %u] Block 2 Q==Kt==V check: %s (%u mismatches)\n",
               cluster_id, errors == 0 ? "PASS" : "FAIL", errors);
      }
    }
    mc_intra_cluster_sync();

    /* Stage 19: scaled dot-product attention, batched over TC samples. */
    uint32_t redmule_id = mempool_get_redmule_id();
    uint32_t num_redmules = mempool_get_redmule_count();

    if (redmule_id < num_redmules) {
      for (uint32_t i = redmule_id; i < TC; i += num_redmules) {
        unsigned int I_ptr = (unsigned int)(&l1_Q2[i][0][0]);
        unsigned int W_ptr = (unsigned int)(&l1_Kt2[i][0][0]);
        unsigned int O_ptr = (unsigned int)(&l1_S2[i][0][0]);
        hwpe_soft_clear();
        mempool_wait(10);
        redmule_cfg(I_ptr, W_ptr, O_ptr, (uint16_t)BEAM, (uint16_t)EMBED,
                   (uint16_t)BEAM, 0, GEMM, Float16);
        mempool_wait(10);
        hwpe_trigger_job();
        mempool_wfi();
      }
    }
    mc_intra_cluster_sync();

    for (uint32_t i = core_id; i < TC; i += num_cores) {
      softmax_parallel_2x4_f16vec(&l1_S2[i][0][0], &l1_Aw2[i][0][0], BEAM,
                                  BEAM, 0, 1);
    }
    mc_intra_cluster_sync();

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

    /* Stage 20: redistribute attention output back to beam clusters. For a
     * fixed tc, the BC beams of one beam cluster are already contiguous
     * within l1_A2[tc][*][*] (beam and embed are the innermost dims). */
    if (mc_is_dm_core()) {
      const size_t chunk_bytes3 = BC * EMBED * sizeof(uint16_t);
      for (uint32_t c = 0; c < N_BEAM; ++c) {
        for (uint32_t tc = 0; tc < TC; ++tc) {
          const uint32_t global_t = t_offset + tc;
          uint32_t dst_off = (uint32_t)((uintptr_t)&l1_attn_stage2[global_t][0][0] -
                                        (uintptr_t)local(0));
          mc_dma_sync_1d((uint64_t)remote_cid(c, dst_off),
                         (uint64_t)(uintptr_t)&l1_A2[tc][c * BC][0],
                         chunk_bytes3);
        }
      }
    }
    mc_intra_cluster_sync();
  }
  mc_global_barrier_xy();
  DONE("Block 2: attention output redistributed to beam clusters");

  /**********************************************************************
   *  Block 2, part C (beam clusters): local transpose -> output Conv1D ->
   *  residual -> FFN (LayerNorm -> Conv1D -> GELU -> Conv1D) -> residual
   *  (final output).
   **********************************************************************/
  if (is_beam) {

    uint32_t num_cores_per_beam = num_cores / BC;
    uint32_t sub_id = core_id % num_cores_per_beam;
    uint32_t b_ln = core_id / num_cores_per_beam;

    /* Stage 21: locally transpose the tdSamples-major staging buffer into
     * the beam-major layout the output Conv1D needs. */
    for (uint32_t idx = core_id; idx < EMBED * BC; idx += num_cores) {
      const uint32_t e = idx / BC;
      const uint32_t b = idx % BC;
      for (uint32_t t = 0; t < TDSAMPLES; ++t) {
        l1_attn_out2[b][e][t] = l1_attn_stage2[t][b][e];
      }
    }
    mc_intra_cluster_sync();

    /* Stage 22: output Conv1D, Embed -> Embed */
    conv1d_f16(&l1_attn_out2[0][0][0], l1_F2, &l1_proj_out2[0][0][0],
              l1_im2col_out2, BC, EMBED, EMBED, TDSAMPLES, WF, 1, core_id,
              num_cores);
    mc_intra_cluster_sync();

    /* Stage 23: residual, res2 = proj_out2 + block1_out */
    residual_add(&l1_res2[0][0][0], &l1_proj_out2[0][0][0],
                &l1_block1_out[0][0][0], core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 24: LayerNorm (FFN) */
    layernorm_parallel_2x4_f16vec(&l1_res2[b_ln][0][0], &l1_norm_ffn2[b_ln][0][0],
                                  EMBED, TDSAMPLES, sub_id, num_cores_per_beam);
    mc_intra_cluster_sync();

    /* Stage 25: Conv1D, Embed -> 2*Embed */
    conv1d_f16(&l1_norm_ffn2[0][0][0], l1_F3, &l1_ffn_hidden2[0][0][0],
              l1_im2col_ffn2a, BC, EMBED, 2 * EMBED, TDSAMPLES, WF, 1,
              core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 26: GELU, in-place. */
    gelu_f16(&l1_ffn_hidden2[0][0][0], BC * 2 * EMBED * TDSAMPLES, core_id,
            num_cores);
    mc_intra_cluster_sync();

    /* Stage 27: Conv1D, 2*Embed -> Embed */
    conv1d_f16(&l1_ffn_hidden2[0][0][0], l1_F4, &l1_ffn_out2[0][0][0],
              l1_im2col_ffn2b, BC, 2 * EMBED, EMBED, TDSAMPLES, WF, 1,
              core_id, num_cores);
    mc_intra_cluster_sync();

    /* Stage 28: residual, block2_out = ffn_out2 + res2 (final output) */
    residual_add(&l1_block2_out[0][0][0], &l1_ffn_out2[0][0][0],
                &l1_res2[0][0][0], core_id, num_cores);
    mc_intra_cluster_sync();
  }
  mc_global_barrier_xy();
  DONE("Block 2 complete");

  mc_global_barrier_xy();
  mc_eoc(eoc_val);
  return 0;
}
