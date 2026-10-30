// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library implements a normalization matrix based on the LayerNorm.
 * A is the M x N input matrix, B stores the normalized A matrix
 */

#pragma once
#include "builtins_v2.h"

/* 32-bit word (two fp16) that may alias the fp16 buffers */
typedef uint32_t __attribute__((may_alias)) layernorm_w32_t;

static inline uint32_t layernorm_v2h_bits(v2h a) {
  union {
    v2h v;
    uint32_t u;
  } x = {a};
  return x.u;
}

/* Stores the normalized words n0, n1 (elements j..j+3) of a row as the three
 * rows of its 1D im2col with Wf = 3 (x[t-1], x[t], x[t+1], zero padded), the
 * layout of im2col1d_f16. prev is the word before n0 (0 at the row start).
 * Word w of row x[t-1] equals word w-1 of row x[t+1]. */
static inline void layernorm_im2col_w3_store(layernorm_w32_t *out, uint32_t Ww,
                                             uint32_t w, uint32_t prev,
                                             v2h n0v, v2h n1v) {
  uint32_t n0 = layernorm_v2h_bits(n0v), n1 = layernorm_v2h_bits(n1v);
  uint32_t s0 = (prev >> 16) | (n0 << 16), s1 = (n0 >> 16) | (n1 << 16);
  out[w] = s0;
  out[w + 1] = s1;
  out[Ww + w] = n0;
  out[Ww + w + 1] = n1;
  if (w > 0) {
    out[2 * Ww + w - 1] = s0;
  }
  out[2 * Ww + w] = s1;
  if (w + 2 == Ww) {
    out[2 * Ww + w + 1] = n1 >> 16;
  }
}

/* Inlined in each variant, so that im2col_w3 is a constant there */
static inline __attribute__((always_inline)) void
layernorm_parallel_2x4_f16vec_body(const __fp16 *__restrict__ A,
                                   __fp16 *__restrict__ B, uint32_t M,
                                   uint32_t N, uint32_t core_id,
                                   uint32_t numThreads, uint32_t im2col_w3) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  float InvN = 1.0f / (float)N;
  v2h vInvN;

  asm volatile("vfcpka.h.s %[vInvN], %[InvN], %[InvN];"
               : [vInvN] "+&r"(vInvN)
               : [InvN] "r"(InvN));

  for (i = core_id * 2; i < M; i += numThreads * 2) {
    v2h vSumMean0 = (v2h)0.0f, vSumMean1 = (v2h)0.0f;
    v2h vSumSq0 = (v2h)0.0f, vSumSq1 = (v2h)0.0f;

    for (j = 0; j < N; j += 4) {
      v2h aVec00 = *(v2h *)&(A[i * N + j]);
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);
      // Variables used to store square of loaded aVec01 and aVec11
      v2h aVecSq01, aVecSq11;
      asm volatile(
          // 1) Accumulate sum(x): Accumulate aVeci0 and aVeci1 in vSumi
          // 2) Accumulate sum(x^2): Square aVecji and then accumulate in
          // vSumSqi
          "vfadd.h %[vSum0], %[vSum0], %[aVec00];"
          "vfadd.h %[vSum1], %[vSum1], %[aVec10];"
          "vfmul.h %[aVec00], %[aVec00], %[aVec00];" // aVec00 stores square of
                                                     // loaded aVec00
          "vfmul.h %[aVec10], %[aVec10], %[aVec10];" // aVec10 stores square of
                                                     // loaded aVec10
          "vfmul.h %[aVecSq01], %[aVec01], %[aVec01];"
          "vfmul.h %[aVecSq11], %[aVec11], %[aVec11];"
          "vfadd.h %[vSumSq0], %[vSumSq0], %[aVec00];"
          "vfadd.h %[vSumSq1], %[vSumSq1], %[aVec10];"
          "vfadd.h %[vSum0], %[vSum0], %[aVec01];"
          "vfadd.h %[vSum1], %[vSum1], %[aVec11];"
          "vfadd.h %[vSumSq0], %[vSumSq0], %[aVecSq01];"
          "vfadd.h %[vSumSq1], %[vSumSq1], %[aVecSq11];"
          : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
            [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1),
            [aVecSq01] "+&r"(aVecSq01), [aVecSq11] "+&r"(aVecSq11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    unsigned ShuffleMask = 0x00020003; // [a b] => [b a]
    // Variables used to store temporary sum values
    v2h x0, x1, y0, y1;
    // Reduce vector sum to one sum (replicated 2 times)
    asm volatile(
        "pv.shuffle2.h %[x0],      %[vSum0],   %[ShuffleMask];"
        "pv.shuffle2.h %[x1],      %[vSum1],   %[ShuffleMask];"
        "pv.shuffle2.h %[y0],      %[vSumSq0], %[ShuffleMask];"
        "pv.shuffle2.h %[y1],      %[vSumSq1], %[ShuffleMask];"
        "vfadd.h       %[vSum0],   %[vSum0],   %[x0];"
        "vfadd.h       %[vSum1],   %[vSum1],   %[x1];"
        "vfadd.h       %[vSumSq0], %[vSumSq0], %[y0];"
        "vfadd.h       %[vSumSq1], %[vSumSq1], %[y1];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [y0] "+&r"(y0), [y1] "+&r"(y1)
        : [ShuffleMask] "r"(ShuffleMask));

    // Compute variance
    asm volatile(
        // Compute E[x] = sum / N
        "vfmul.h  %[vSum0], %[vSum0], %[vInvN];"
        "vfmul.h  %[vSum1], %[vSum1], %[vInvN];"
        // Compute E[x^2] = sum^2 / N
        "vfmul.h  %[x0], %[vSumSq0], %[vInvN];"
        "vfmul.h  %[x1], %[vSumSq1], %[vInvN];"
        // Compute E[x]^2
        "vfmul.h  %[y0], %[vSum0], %[vSum0];"
        "vfmul.h  %[y1], %[vSum1], %[vSum1];"
        // Compute var = E[x^2] - E[x]^2
        "vfsub.h  %[x0], %[x0], %[y0];"
        "vfsub.h  %[x1], %[x1], %[y1];"
        // Compute the square root of Var: std = sqrt(var)
        // "vfsqrt.h      %[vSumSq0], %[x0];"
        // "vfsqrt.h      %[vSumSq1], %[x1];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [y0] "+&r"(y0), [y1] "+&r"(y1)
        : [vInvN] "r"(vInvN));

    uint32_t prev0 = 0, prev1 = 0;
    for (j = 0; j < N; j += 4) {
      // aVec<r><k>: row i + r, elements j + 2k and j + 2k + 1
      v2h aVec00 = *(v2h *)&(A[i * N + j]);
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);
      asm volatile(
          // Compute: aVec0 - vMean
          "vfsub.h %[aVec00], %[aVec00], %[vMean0];"
          "vfsub.h %[aVec01], %[aVec01], %[vMean0];"
          "vfsub.h %[aVec10], %[aVec10], %[vMean1];"
          "vfsub.h %[aVec11], %[aVec11], %[vMean1];"
          // Compute: aNorm0 / vStd
          "vfdiv.h %[aVec00], %[aVec00], %[vStd0];"
          "vfdiv.h %[aVec01], %[aVec01], %[vStd0];"
          "vfdiv.h %[aVec10], %[aVec10], %[vStd1];"
          "vfdiv.h %[aVec11], %[aVec11], %[vStd1];"
          : [aVec00] "+r"(aVec00), [aVec01] "+r"(aVec01), [aVec10] "+r"(aVec10),
            [aVec11] "+r"(aVec11)
          : [vMean0] "r"(vSumMean0), [vMean1] "r"(vSumMean1),
            [vStd0] "r"(vSumSq0), [vStd1] "r"(vSumSq1));
      if (im2col_w3) {
        layernorm_w32_t *B0 = (layernorm_w32_t *)&B[i * 3 * N];
        layernorm_w32_t *B1 = (layernorm_w32_t *)&B[(i + 1) * 3 * N];
        layernorm_im2col_w3_store(B0, N / 2, j / 2, prev0, aVec00, aVec01);
        layernorm_im2col_w3_store(B1, N / 2, j / 2, prev1, aVec10, aVec11);
        prev0 = layernorm_v2h_bits(aVec01);
        prev1 = layernorm_v2h_bits(aVec11);
      } else {
        (*(v2h *)&B[i * N + j]) = aVec00;
        (*(v2h *)&B[i * N + j + 2]) = aVec01;
        (*(v2h *)&B[(i + 1) * N + j]) = aVec10;
        (*(v2h *)&B[(i + 1) * N + j + 2]) = aVec11;
      }
    }
  }
}

void layernorm_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                   __fp16 *__restrict__ B, uint32_t M,
                                   uint32_t N, uint32_t core_id,
                                   uint32_t numThreads) {
  layernorm_parallel_2x4_f16vec_body(A, B, M, N, core_id, numThreads, 0);
}

/* Same normalization, with B written as the 1D im2col (Wf = 3) of the M x N
 * output, 3 * M x N, as im2col1d_f16 writes it. N is a multiple of 4. */
void layernorm_im2col_w3_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                             __fp16 *__restrict__ B,
                                             uint32_t M, uint32_t N,
                                             uint32_t core_id,
                                             uint32_t numThreads) {
  layernorm_parallel_2x4_f16vec_body(A, B, M, N, core_id, numThreads, 1);
}
