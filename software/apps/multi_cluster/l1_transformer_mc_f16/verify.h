// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
 * the reference uses soft-float. */
#ifndef CHK_NUMERIC_BATCHES
#define CHK_NUMERIC_BATCHES (1)
#endif
static uint16_t chk_smp[CHK_MAX][CHK_SAMPLES] L1_LOCAL;

/* Hash of the n halfwords of buf, computed bitwise on core 0, and
 * CHK_SAMPLES evenly spaced values of buf, recorded under (label, idx). */  
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

/* Recomputes rows of P = softmax(Q * Kt) of one batch on core 0 (rows in
 * different slices) and records the number of outputs off by more than
 * 2e-3 + 2% of the reference, and the largest error (x1e4). The reference
 * follows softmax_parallel_2x4_f16vec: row maximum starting from 0.5 and
 * exp(x) approximated by 1 + x + 0.5 x^2 + 0.167 x^3. */
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
      float m = 0.5f, sum = 0.0f;
      for (uint32_t k = 0; k < S; k++) {
        float acc = 0.0f;
        for (uint32_t j = 0; j < W; j++) {
          acc += h2f(&Q[r * W + j]) * h2f(&Kt[j * S + k]);
        }
        sc[k] = acc;
        m = acc > m ? acc : m;
      }
      for (uint32_t k = 0; k < S; k++) {
        float x = sc[k] - m;
        sc[k] = 1.0f + x + 0.5f * x * x + 0.167f * x * x * x;
        sum += sc[k];
      }
      for (uint32_t k = 0; k < S; k++) {
        float ref = sc[k] / sum;
        float d = h2f(&P[r * S + k]) - ref;
        float ref_abs = ref < 0 ? -ref : ref;
        if (d < 0)
          d = -d;
        if (d > 2e-3f + 0.02f * ref_abs)
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
