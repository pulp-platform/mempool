// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library applies a softmax over an entire matrix.
 * A is the M x N input matrix, B stores the resulting matrix
 */

#pragma once
#include "builtins_v2.h"

void softmax_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                 __fp16 *__restrict__ B, uint32_t M, uint32_t N,
                                 uint32_t core_id, uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  const unsigned ShuffleMask = 0x00030002; // [a b] => [b a]
  v2h vDiv16, vDiv12, vOne;
  __VFCPKAHS(&vDiv16, 0.167f, 0.167f);
  __VFCPKAHS(&vDiv12, 0.5f, 0.5f);
  __VFCPKAHS(&vOne, 1.0f, 1.0f);

  for (i = core_id * 2; i < M; i += numThreads * 2) {

    /* 1) Find the row-wise maximum value */

    v2h max0 = vDiv12;
    v2h max1 = vDiv12;
    v2h x0, x1;

    for (j = 0; j < N; j += 4) {
      v2h aVec00 = *(v2h *)&(A[i * N + j]);           // aVec00 = [a01 a00]
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);       // aVec01 = [a03 a02]
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);     // aVec10 = [a11 a10]
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]); // aVec11 = [a13 a12]
      asm volatile(
          // Find max value (no full reduction)
          "vfmax.h %[tmp0], %[aVec00], %[aVec01];"
          "vfmax.h %[tmp1], %[aVec10], %[aVec11];"
          "vfmax.h %[max0], %[max0], %[tmp0];"
          "vfmax.h %[max1], %[max1], %[tmp1];"
          : [max0] "+&r"(max0), [max1] "+&r"(max1), [tmp0] "+&r"(x0),
            [tmp1] "+&r"(x1)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.h %[tmp0], %[max0], %[ShuffleMask];"
        "pv.shuffle2.h %[tmp1], %[max1], %[ShuffleMask];"
        "vfmax.h       %[max0], %[tmp0], %[max0];"
        "vfmax.h       %[max1], %[tmp1], %[max1];"
        : [max0] "+&r"(max0), [max1] "+&r"(max1), [tmp0] "+&r"(x0),
          [tmp1] "+&r"(x1)
        : [ShuffleMask] "r"(ShuffleMask));

    /* 2) Compute exp(x - max) */

    // Store sum value in x0, x1
    x0 = (v2h)0.0f;
    x1 = (v2h)0.0f;

    for (j = 0; j < N; j += 4) {
      v2h aVec00 = *(v2h *)&(A[i * N + j]);
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);

      // Compute x' = x - max(x)
      asm volatile("vfsub.h %[aVec00], %[aVec00], %[max0];"
                   "vfsub.h %[aVec01], %[aVec01], %[max0];"
                   "vfsub.h %[aVec10], %[aVec10], %[max1];"
                   "vfsub.h %[aVec11], %[aVec11], %[max1];"
                   : [aVec00] "+&r"(aVec00), [aVec01] "+&r"(aVec01),
                     [aVec10] "+&r"(aVec10), [aVec11] "+&r"(aVec11)
                   : [max0] "r"(max0), [max1] "r"(max1));

      v2h xCu00, xCu01, xCu10, xCu11;
      v2h exp00, exp01, exp10, exp11;

      // Approximate exp with Taylor Series
      asm volatile(
          "vfmul.h %[xSq00], %[aVec00], %[aVec00];" // x^2
          "vfmul.h %[xSq01], %[aVec01], %[aVec01];"
          "vfmul.h %[xSq10], %[aVec10], %[aVec10];"
          "vfmul.h %[xSq11], %[aVec11], %[aVec11];"
          "vfmul.h %[xCu00], %[xSq00], %[aVec00];" // x^3
          "vfmul.h %[xCu01], %[xSq01], %[aVec01];"
          "vfmul.h %[xCu10], %[xSq10], %[aVec10];"
          "vfmul.h %[xCu11], %[xSq11], %[aVec11];"
          "vfmul.h %[xSq00], %[xSq00], %[vDiv12];" // 0.5*x^2
          "vfmul.h %[xSq01], %[xSq01], %[vDiv12];"
          "vfmul.h %[xSq10], %[xSq10], %[vDiv12];"
          "vfmul.h %[xSq11], %[xSq11], %[vDiv12];"
          "vfmul.h %[xCu00], %[xCu00], %[vDiv16];" // 0.167*x^3
          "vfmul.h %[xCu01], %[xCu01], %[vDiv16];"
          "vfmul.h %[xCu10], %[xCu10], %[vDiv16];"
          "vfmul.h %[xCu11], %[xCu11], %[vDiv16];"
          "vfmac.h %[xSq00], %[aVec00], %[vOne];" // 1*x + 0.5*x^2
          "vfmac.h %[xSq01], %[aVec01], %[vOne];"
          "vfmac.h %[xSq10], %[aVec10], %[vOne];"
          "vfmac.h %[xSq11], %[aVec11], %[vOne];"
          "vfadd.h %[xSq00], %[xSq00], %[vOne];" // 1 + 1*x + 0.5*x^2
          "vfadd.h %[xSq01], %[xSq01], %[vOne];"
          "vfadd.h %[xSq10], %[xSq10], %[vOne];"
          "vfadd.h %[xSq11], %[xSq11], %[vOne];"
          "vfadd.h %[xSq00], %[xSq00], %[xCu00];" // 1 + 1*x + 0.5*x^2 +
                                                  // 0.167*x^3
          "vfadd.h %[xSq01], %[xSq01], %[xCu01];"
          "vfadd.h %[xSq10], %[xSq10], %[xCu10];"
          "vfadd.h %[xSq11], %[xSq11], %[xCu11];"
          : [xSq00] "+&r"(exp00), [xSq01] "+&r"(exp01), [xSq10] "+&r"(exp10),
            [xSq11] "+&r"(exp11), [xCu00] "+&r"(xCu00), [xCu01] "+&r"(xCu01),
            [xCu10] "+&r"(xCu10), [xCu11] "+&r"(xCu11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11), [vDiv16] "r"(vDiv16), [vDiv12] "r"(vDiv12),
            [vOne] "r"(vOne));

      // Compute row-wise sum of all exponents
      asm volatile("vfadd.h %[tmp0], %[exp00], %[exp01];" // Use aVec00/10 as
                                                          // temporary sum
                   "vfadd.h %[tmp1], %[exp10], %[exp11];"
                   "vfadd.h %[vSum0], %[vSum0], %[tmp0];"
                   "vfadd.h %[vSum1], %[vSum1], %[tmp1];"
                   : [vSum0] "+&r"(x0), [vSum1] "+&r"(x1), [tmp0] "+&r"(aVec00),
                     [tmp1] "+&r"(aVec10)
                   : [exp00] "r"(exp00), [exp01] "r"(exp01), [exp10] "r"(exp10),
                     [exp11] "r"(exp11));

      // Store temporary variables
      (*(v2h *)&B[i * N + j]) = exp00;
      (*(v2h *)&B[i * N + j + 2]) = exp01;
      (*(v2h *)&B[(i + 1) * N + j]) = exp10;
      (*(v2h *)&B[(i + 1) * N + j + 2]) = exp11;
    }

    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.h %[tmp0],  %[vSum0], %[ShuffleMask];" // Use max0/1 as
                                                            // temporary sum
        "pv.shuffle2.h %[tmp1],  %[vSum1], %[ShuffleMask];"
        "vfadd.h       %[vSum0], %[vSum0], %[tmp0];"
        "vfadd.h       %[vSum1], %[vSum1], %[tmp1];"
        : [vSum0] "+&r"(x0), [vSum1] "+&r"(x1), [tmp0] "+&r"(max0),
          [tmp1] "+&r"(max1)
        : [ShuffleMask] "r"(ShuffleMask));

    /* 3) Multiply by the reciprocal of the row-wise sum */

    // One division per row, instead of one per pair of elements
    v2h inv0, inv1;
    asm volatile("vfdiv.h %[inv0], %[vOne], %[vSum0];"
                 "vfdiv.h %[inv1], %[vOne], %[vSum1];"
                 : [inv0] "=&r"(inv0), [inv1] "=&r"(inv1)
                 : [vOne] "r"(vOne), [vSum0] "r"(x0), [vSum1] "r"(x1));

    for (j = 0; j < N; j += 4) {
      v2h bVec00 = *(v2h *)&(B[i * N + j]);
      v2h bVec01 = *(v2h *)&(B[i * N + j + 2]);
      v2h bVec10 = *(v2h *)&(B[(i + 1) * N + j]);
      v2h bVec11 = *(v2h *)&(B[(i + 1) * N + j + 2]);

      //  Compute softmax = exp * (1 / sum_exp)
      asm volatile("vfmul.h %[bVec00], %[bVec00], %[inv0];"
                   "vfmul.h %[bVec01], %[bVec01], %[inv0];"
                   "vfmul.h %[bVec10], %[bVec10], %[inv1];"
                   "vfmul.h %[bVec11], %[bVec11], %[inv1];"
                   : [bVec00] "+&r"(bVec00), [bVec01] "+&r"(bVec01),
                     [bVec10] "+&r"(bVec10), [bVec11] "+&r"(bVec11)
                   : [inv0] "r"(inv0), [inv1] "r"(inv1));

      (*(v2h *)&B[i * N + j]) = bVec00;
      (*(v2h *)&B[i * N + j + 2]) = bVec01;
      (*(v2h *)&B[(i + 1) * N + j]) = bVec10;
      (*(v2h *)&B[(i + 1) * N + j + 2]) = bVec11;
    }
  }
}

/* Online (running) softmax, same rows, parallelization and exp approximation
 * as softmax_parallel_2x4_f16vec. Pass 1 reads each row once and keeps, per
 * vector lane, the running maximum m and the running sum s of exp(x - m):
 * when m grows, s is rescaled by exp(m_old - m_new). The two lanes are then
 * merged into the row maximum and sum. Pass 2 writes exp(x - m) / s. */

static inline v2h sm_vadd(v2h a, v2h b) {
  v2h r;
  asm("vfadd.h %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  return r;
}
static inline v2h sm_vsub(v2h a, v2h b) {
  v2h r;
  asm("vfsub.h %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  return r;
}
static inline v2h sm_vmul(v2h a, v2h b) {
  v2h r;
  asm("vfmul.h %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  return r;
}
static inline v2h sm_vmax(v2h a, v2h b) {
  v2h r;
  asm("vfmax.h %0, %1, %2" : "=r"(r) : "r"(a), "r"(b));
  return r;
}
/* [a b] -> [b a] */
static inline v2h sm_vswap(v2h a) {
  union {
    v2h v;
    uint32_t u;
  } x = {a};
  x.u = (x.u >> 16) | (x.u << 16);
  return x.v;
}
/* exp(x) ~ 1 + x + 0.5 x^2 + 0.167 x^3 */
static inline v2h sm_vexp(v2h x, v2h one, v2h c2, v2h c3) {
  v2h x2 = sm_vmul(x, x);
  v2h r = sm_vadd(sm_vadd(one, x), sm_vmul(x2, c2));
  return sm_vadd(r, sm_vmul(sm_vmul(x2, x), c3));
}

void softmax_online_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                        __fp16 *__restrict__ B, uint32_t M,
                                        uint32_t N, uint32_t core_id,
                                        uint32_t numThreads) {
  v2h zero, one, c2, c3;
  __VFCPKAHS(&zero, 0.0f, 0.0f);
  __VFCPKAHS(&one, 1.0f, 1.0f);
  __VFCPKAHS(&c2, 0.5f, 0.5f);
  __VFCPKAHS(&c3, 0.167f, 0.167f);

  for (uint32_t i = core_id * 2; i < M; i += numThreads * 2) {
    const __fp16 *a0 = &A[i * N], *a1 = &A[(i + 1) * N];
    __fp16 *b0 = &B[i * N], *b1 = &B[(i + 1) * N];

    /* 1) Running maximum and sum of exp(x - max), per lane */
    v2h m0 = c2, m1 = c2, s0 = zero, s1 = zero;
    for (uint32_t j = 0; j < N; j += 4) {
      v2h x00 = *(v2h *)&a0[j], x01 = *(v2h *)&a0[j + 2];
      v2h x10 = *(v2h *)&a1[j], x11 = *(v2h *)&a1[j + 2];
      v2h n0 = sm_vmax(m0, sm_vmax(x00, x01));
      v2h n1 = sm_vmax(m1, sm_vmax(x10, x11));
      s0 = sm_vadd(sm_vmul(s0, sm_vexp(sm_vsub(m0, n0), one, c2, c3)),
                   sm_vadd(sm_vexp(sm_vsub(x00, n0), one, c2, c3),
                           sm_vexp(sm_vsub(x01, n0), one, c2, c3)));
      s1 = sm_vadd(sm_vmul(s1, sm_vexp(sm_vsub(m1, n1), one, c2, c3)),
                   sm_vadd(sm_vexp(sm_vsub(x10, n1), one, c2, c3),
                           sm_vexp(sm_vsub(x11, n1), one, c2, c3)));
      m0 = n0;
      m1 = n1;
    }

    /* Merge the lanes: row maximum in both lanes, then 1 / row sum */
    v2h r0 = sm_vmax(m0, sm_vswap(m0)), r1 = sm_vmax(m1, sm_vswap(m1));
    s0 = sm_vmul(s0, sm_vexp(sm_vsub(m0, r0), one, c2, c3));
    s1 = sm_vmul(s1, sm_vexp(sm_vsub(m1, r1), one, c2, c3));
    s0 = sm_vadd(s0, sm_vswap(s0));
    s1 = sm_vadd(s1, sm_vswap(s1));
    v2h inv0, inv1;
    asm volatile("vfdiv.h %[inv0], %[one], %[s0];"
                 "vfdiv.h %[inv1], %[one], %[s1];"
                 : [inv0] "=&r"(inv0), [inv1] "=&r"(inv1)
                 : [one] "r"(one), [s0] "r"(s0), [s1] "r"(s1));

    /* 2) exp(x - max) / sum */
    for (uint32_t j = 0; j < N; j += 4) {
      *(v2h *)&b0[j] =
          sm_vmul(sm_vexp(sm_vsub(*(v2h *)&a0[j], r0), one, c2, c3), inv0);
      *(v2h *)&b0[j + 2] =
          sm_vmul(sm_vexp(sm_vsub(*(v2h *)&a0[j + 2], r0), one, c2, c3), inv0);
      *(v2h *)&b1[j] =
          sm_vmul(sm_vexp(sm_vsub(*(v2h *)&a1[j], r1), one, c2, c3), inv1);
      *(v2h *)&b1[j + 2] =
          sm_vmul(sm_vexp(sm_vsub(*(v2h *)&a1[j + 2], r1), one, c2, c3), inv1);
    }
  }
}
