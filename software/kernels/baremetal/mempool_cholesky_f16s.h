// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich
// Author: Bowen Wang, ETH Zurich

#pragma once
#include "builtins_v2.h"

#ifdef __XDIVSQRT

/**
  @brief         Cholesky decomposition with Crout algorithm.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @param[in]     folded matrices are folded row-wise in memory
  @return        none
*/
void mempool_cholesky_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n,
                           const uint32_t folded) {

  __fp16 sum;
  __fp16 a, b;
  __fp16 c, d;
  __fp16 diag;   // Diagonal element
  __fp16 ap, bp; // Pivot element
  __fp16 as, bs; // Sum element
  uint32_t i, j, k;
  const uint32_t offset = folded ? NUM_BANKS : n;

  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * offset + j)];
    sum = (__fp16)0.0f;
    for (k = 0; k < j; k++) {
      a = pL[2U * (j * offset + k)];
      b = pL[2U * (j * offset + k) + 1];
      asm volatile("fmadd.h %[sum], %[a], %[a], %[sum];"
                   "fmadd.h %[sum], %[b], %[b], %[sum];"
                   : [sum] "+&r"(sum)
                   : [a] "r"(a), [b] "r"(b)
                   :);
    }
    asm volatile("fsub.h %[ap], %[ap], %[sum];"
                 "fsqrt.h  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
    pL[2U * (j * offset + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * offset + j)];
      bp = pSrc[2U * (i * offset + j) + 1];
      // Diag
      diag = pL[2U * (j * offset + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (__fp16)0.0f;
      bs = (__fp16)0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (i * offset + k)];
        b = pL[2U * (i * offset + k) + 1];
        c = pL[2U * (j * offset + k)];
        d = pL[2U * (j * offset + k) + 1];
        asm volatile("fmadd.h %[as], %[a], %[c], %[as];"
                     "fmadd.h %[as], %[b], %[d], %[as];"
                     "fmadd.h %[bs], %[b], %[c], %[bs];"
                     "fnmsub.h %[bs], %[a], %[d], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
      asm volatile("fsub.h %[ap], %[ap], %[as];"
                   "fsub.h %[bp], %[bp], %[bs];"
                   "fdiv.h %[ap], %[ap], %[diag];"
                   "fdiv.h %[bp], %[bp], %[diag];"
                   : [ap] "+&r"(ap), [bp] "+&r"(bp)
                   : [diag] "r"(diag), [as] "r"(as), [bs] "r"(bs)
                   :);
      pL[2U * (i * offset + j)] = ap;
      pL[2U * (i * offset + j) + 1] = bp;
    }
  }
  return;
}

/** VECTORIZED CODE
  @brief         Cholesky decomposition with Crout algorithm.
  Output data is folded to the core's local memory.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_f16vecs(__fp16 *pSrc, __fp16 *pL, const uint32_t n,
                              const uint32_t folded) {

  __fp16 diag;
  v2h apbp, dgdg;
  v2h ab, cd;
  uint32_t i, j, k;
  const uint32_t offset = folded ? NUM_BANKS : n;

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    __fp16 ap = pSrc[2U * (j * offset + j)];
    float sum = 0.0f;
    for (k = 0; k < j; k++) {
      ab = (*(v2h *)&pL[2U * (j * offset + k)]);
      asm volatile("vfdotpex.s.h %0, %1, %1;" : "+&r"(sum) : "r"(ab) :);
    }
    asm volatile("fcvt.h.s %0, %0;" : "+&r"(sum) :);
    asm volatile("fsub.h   %0, %0, %1;" : "+&r"(ap) : "r"(sum));
    asm volatile("fsqrt.h  %0, %0;" : "+&r"(ap) :);
    pL[2U * (j * offset + j)] = ap;

    // Elements on rows
    uint32_t __srt_iloop__ = (j + 1);
    uint32_t __end_kloop__ = j;
#ifdef __CDOTP
    for (i = __srt_iloop__; i < n; i++) {
      apbp = (*(v2h *)&pSrc[2U * (i * offset + j)]); // Pivot
      diag = pL[2U * (j * offset + j)];              // Diag
      v2h asbs = (v2h)0.0f;
      float as = 0.0f;
      float bs = 0.0f;
      for (k = 0; k < __end_kloop__; k++) {
        ab = (*(v2h *)&pL[2U * (i * offset + k)]);
        cd = (*(v2h *)&pL[2U * (j * offset + k)]);
        asm volatile("fccdotpex.s.h  %0, %1, %2;"
                     : "+&r"(asbs)
                     : "r"(cd), "r"(ab));
        //        asm volatile("fcndotpex.s.h  %0, %1, %2;"
        //                     : "+&r"(asbs)
        //                     : "r"(cd), "r"(ab));
      }
      asm volatile("pv.shuffle2.h %0, %0, %[mask];"
                   : "+&r"(asbs)
                   : [mask] "r"(0x00020003));
      asm volatile("pv.pack %0, %1, %1;" : "+&r"(dgdg) : "r"(diag));
      asm volatile("vfsub.h %0, %0, %1;" : "+&r"(apbp) : "r"(asbs));
      asm volatile("vfdiv.h %0, %0, %1;" : "+&r"(apbp) : "r"(dgdg));
      (*(v2h *)&pL[2U * (i * offset + j)]) = apbp;
    }
#else
    for (i = __srt_iloop__; i < n; i++) {
      apbp = (*(v2h *)&pSrc[2U * (i * offset + j)]); // Pivot
      diag = pL[2U * (j * offset + j)];              // Diag
      float as = 0.0f;
      float bs = 0.0f;
      v2h asbs;
      for (k = 0; k < __end_kloop__; k++) {
        ab = (*(v2h *)&pL[2U * (i * offset + k)]);
        cd = (*(v2h *)&pL[2U * (j * offset + k)]);
        v2h ndc;
        const uint32_t neg_mask = 0x00008000;
        const uint32_t shuffle_mask = 0x00020003;
        asm volatile(
            // s = s + (ac + bd) + j(bc - ad)
            "vfdotpex.s.h  %[as],  %[ab], %[cd];"
            "pv.shuffle2.h %[ndc], %[cd], %[shuffle_mask];"
            "xor           %[ndc], %[neg_mask], %[ndc];"
            "vfdotpex.s.h  %[bs],  %[ab], %[ndc];"
            : [as] "+&r"(as), [bs] "+&r"(bs), [ndc] "+r"(ndc)
            : [ab] "r"(ab), [cd] "r"(cd), [neg_mask] "r"(neg_mask),
              [shuffle_mask] "r"(shuffle_mask)
            :);
      }
      asm volatile("vfcpka.h.s %0, %1, %2;" : "+&r"(asbs) : "r"(as), "r"(bs));
      asm volatile("pv.pack    %0, %1, %1;" : "+&r"(dgdg) : "r"(diag));
      asm volatile("vfsub.h    %0, %0, %1;" : "+&r"(apbp) : "r"(asbs));
      asm volatile("vfdiv.h    %0, %0, %1;" : "+&r"(apbp) : "r"(dgdg));
      (*(v2h *)&pL[2U * (i * offset + j)]) = apbp;
    }
#endif
  }
  return;
}

/** VECTORIZED CODE with unrolled inner loop
  @brief         Cholesky decomposition with Crout algorithm.
  Output data is folded to the core's local memory.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_f16vecs_unroll4(__fp16 *pSrc, __fp16 *pL,
                                      const uint32_t n) {

  float sum;   // register float sum
  __fp16 diag; // Diagonal element
  __fp16 ap;

  float as1, as2, as3, as4;
  float bs1, bs2, bs3, bs4;

  v2h abp;
  v2h abp1, abp2, abp3, abp4;
  v2h ab1, ab2, ab3, ab4, cd;
  v2h diagdiag;

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * n + j)];
    sum = (float)0.0f;
    for (k = 0; k < j; k++) {
      ab1 = (*(v2h *)&pL[2U * (j * n + k)]);
      asm volatile("vfdotpex.s.h %0, %1, %1;" : "+&r"(sum) : "r"(ab1) :);
    }
    asm volatile("fcvt.h.s %0, %0;" : "+&r"(sum) :);
    asm volatile("fsub.h   %0, %0, %1;" : "+&r"(ap) : "r"(sum));
    asm volatile("fsqrt.h  %0, %0;" : "+&r"(ap) :);
    pL[2U * (j * n + j)] = ap;

    // Elements on rows
    // calculate the first several elements based on number of columns

    uint32_t bound = (j + (n - j - 1) % 4 + 1);
    for (i = j + 1; i < bound; i++) {
      // Pivot
      abp = (*(v2h *)&pSrc[2U * (i * n + j)]);
      // Diag
      diag = pL[2U * (j * n + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as1 = (float)0.0f;
      bs1 = (float)0.0f;
      for (k = 0; k < j; k++) {
        ab1 = (*(v2h *)&pL[2U * (i * n + k)]);
        cd = (*(v2h *)&pL[2U * (j * n + k)]);
        const uint32_t neg_mask = 0x00008000;
        const uint32_t shuffle_mask = 0x00020003;
        asm volatile(
            // s = s + (ac + bd) + j(bc - ad)
            "vfdotpex.s.h  %[as1],  %[ab1], %[cd];"
            "pv.shuffle2.h %[cd], %[cd], %[shuffle_mask];"
            "xor %[cd], %[neg_mask], %[cd];"
            "vfdotpex.s.h  %[bs1],  %[ab1], %[cd];"
            : [as1] "+&r"(as1), [bs1] "+&r"(bs1), [cd] "+&r"(cd)
            : [ab1] "r"(ab1), [neg_mask] "r"(neg_mask),
              [shuffle_mask] "r"(shuffle_mask)
            :);
      }

      asm volatile("vfcpka.h.s %[diagdiag], %[as1], %[bs1];"
                   "vfsub.h %[abp], %[abp], %[diagdiag];"
                   "pv.pack.h %[diagdiag], %[diag], %[diag];"
                   "vfdiv.h %[abp], %[abp], %[diagdiag];"
                   : [abp] "+&r"(abp), [diagdiag] "+&r"(diagdiag)
                   : [as1] "r"(as1), [bs1] "r"(bs1), [diag] "r"(diag)
                   :);

      (*(v2h *)&pL[2U * (i * n + j)]) = abp;
    }

    // Unroll the residual by a factor of four
    for (; i < n; i = i + 4) {
      asm volatile("andi %[as1], %[as1], 0;"
                   "andi %[bs1], %[as1], 0;"
                   "andi %[as2], %[as1], 0;"
                   "andi %[bs2], %[as1], 0;"
                   "andi %[as3], %[as1], 0;"
                   "andi %[bs3], %[as1], 0;"
                   "andi %[as4], %[as1], 0;"
                   "andi %[bs4], %[as1], 0;"
                   : [as1] "+&r"(as1), [as2] "+&r"(as2), [as3] "+&r"(as3),
                     [as4] "+&r"(as4), [bs1] "+&r"(bs1), [bs2] "+&r"(bs2),
                     [bs3] "+&r"(bs3), [bs4] "+&r"(bs4)
                   :
                   :);

      for (k = 0; k < j; k++) {
        cd = (*(v2h *)&pL[2U * (j * n + k)]);
        ab1 = (*(v2h *)&pL[2U * (i * n + k)]);
        ab2 = (*(v2h *)&pL[2U * ((i + 1) * n + k)]);
        ab3 = (*(v2h *)&pL[2U * ((i + 2) * n + k)]);
        ab4 = (*(v2h *)&pL[2U * ((i + 3) * n + k)]);

        const uint32_t neg_mask = 0x00008000;
        const uint32_t shuffle_mask = 0x00020003;
        // Row one
        asm volatile(
            // s = s + (ac + bd) + j(bc - ad)
            "vfdotpex.s.h  %[as1],  %[ab1], %[cd];"
            "vfdotpex.s.h  %[as2],  %[ab2], %[cd];"
            "vfdotpex.s.h  %[as3],  %[ab3], %[cd];"
            "vfdotpex.s.h  %[as4],  %[ab3], %[cd];"

            "pv.shuffle2.h %[cd], %[cd], %[shuffle_mask];"
            "xor %[cd], %[neg_mask], %[cd];"

            "vfdotpex.s.h  %[bs1],  %[ab1], %[cd];"
            "vfdotpex.s.h  %[bs2],  %[ab2], %[cd];"
            "vfdotpex.s.h  %[bs3],  %[ab3], %[cd];"
            "vfdotpex.s.h  %[bs4],  %[ab3], %[cd];"
            : [as1] "+&r"(as1), [as2] "+&r"(as2), [as3] "+&r"(as3),
              [as4] "+&r"(as4), [bs1] "+&r"(bs1), [bs2] "+&r"(bs2),
              [bs3] "+&r"(bs3), [bs4] "+&r"(bs4), [cd] "+r"(cd)
            : [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3), [ab4] "r"(ab4),
              [neg_mask] "r"(neg_mask), [shuffle_mask] "r"(shuffle_mask)
            :);
      }

      // Diag
      diag = pL[2U * (j * n + j)];

      // Pivot
      abp1 = (*(v2h *)&pSrc[2U * (i * n + j)]);
      abp2 = (*(v2h *)&pSrc[2U * ((i + 1) * n + j)]);
      abp3 = (*(v2h *)&pSrc[2U * ((i + 2) * n + j)]);
      abp4 = (*(v2h *)&pSrc[2U * ((i + 3) * n + j)]);
      asm volatile("vfcpka.h.s %[diagdiag], %[as1], %[bs1];"
                   "vfcpka.h.s %[diagdiag], %[as2], %[bs2];"
                   "vfcpka.h.s %[diagdiag], %[as3], %[bs3];"
                   "vfcpka.h.s %[diagdiag], %[as4], %[bs4];"

                   "vfsub.h %[abp1], %[abp1], %[diagdiag];"
                   "vfsub.h %[abp2], %[abp2], %[diagdiag];"
                   "vfsub.h %[abp3], %[abp3], %[diagdiag];"
                   "vfsub.h %[abp4], %[abp4], %[diagdiag];"

                   "pv.pack.h %[diagdiag], %[diag], %[diag];"
                   "vfdiv.h %[abp1], %[abp1], %[diagdiag];"
                   "vfdiv.h %[abp2], %[abp2], %[diagdiag];"
                   "vfdiv.h %[abp3], %[abp3], %[diagdiag];"
                   "vfdiv.h %[abp4], %[abp4], %[diagdiag];"

                   "andi %[as1], %[as1], 0;"
                   "andi %[bs1], %[as1], 0;"
                   "andi %[as2], %[as1], 0;"
                   "andi %[bs2], %[as1], 0;"
                   "andi %[as3], %[as1], 0;"
                   "andi %[bs3], %[as1], 0;"
                   "andi %[as4], %[as1], 0;"
                   "andi %[bs4], %[as1], 0;"

                   : [abp1] "+&r"(abp1), [abp2] "+&r"(abp2), [abp3] "+&r"(abp3),
                     [abp4] "+&r"(abp4), [diagdiag] "+&r"(diagdiag),
                     [as1] "+&r"(as1), [as2] "+&r"(as2), [as3] "+&r"(as3),
                     [as4] "+&r"(as4), [bs1] "+&r"(bs1), [bs2] "+&r"(bs2),
                     [bs3] "+&r"(bs3), [bs4] "+&r"(bs4)
                   : [diag] "r"(diag)
                   :);

      (*(v2h *)&pL[2U * (i * n + j)]) = abp1;
      (*(v2h *)&pL[2U * ((i + 1) * n + j)]) = abp2;
      (*(v2h *)&pL[2U * ((i + 2) * n + j)]) = abp3;
      (*(v2h *)&pL[2U * ((i + 3) * n + j)]) = abp4;
    }
  }
  return;
}

#else

/** VECTORIZED CODE
  @brief         Cholesky decomposition with Crout algorithm.
  Output data is folded to the core's local memory.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_f16vecs(__fp16 *pSrc, __fp16 *pL, const uint32_t n,
                              const uint32_t folded) {

  float sum;            // register float sum
  float as, bs;         // real and imaginary sums
  float diag_f32;       // Diagonal element
  float ap_f32, bp_f32; // real and imaginary pivot

  __fp16 diag;   // Diagonal element
  __fp16 ap, bp; // real and imaginary pivot

  v2h asbs;
  v2h ab, cd, ndc;

  uint32_t i, j, k;
  const uint32_t offset = folded ? NUM_BANKS : n;

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * offset + j)];
    asm volatile("fcvt.s.h %0, %1;" : "=r"(sum) : "r"(ap) :);
    for (k = 0; k < j; k++) {
      ab = (*(v2h *)&pL[2U * (j * offset + k)]);
      asm volatile("vfndotpex.s.h %[sum], %[ab], %[ab];"
                   : [sum] "+&r"(sum)
                   : [ab] "r"(ab)
                   :);
    }
    sum = (float)sqrt(sum);
    asm volatile("fcvt.h.s %0, %1;" : "=r"(ap) : "r"(sum) :);
    pL[2U * (j * offset + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * offset + j)];
      bp = pSrc[2U * (i * offset + j + 1)];
      // Diag
      diag = pL[2U * (j * offset + j)];

      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (float)0.0f;
      bs = (float)0.0f;
      asm volatile("fcvt.s.h %0, %1;" : "=r"(ap_f32) : "r"(ap) :);
      asm volatile("fcvt.s.h %0, %1;" : "=r"(bp_f32) : "r"(bp) :);
      asm volatile("fcvt.s.h %0, %1;" : "=r"(diag_f32) : "r"(diag) :);
      for (k = 0; k < j; k++) {
        ab = (*(v2h *)&pL[2U * (i * offset + k)]);
        cd = (*(v2h *)&pL[2U * (j * offset + k)]);
        const uint32_t neg_mask = 0x00008000;
        const uint32_t shuffle_mask = 0x00020003;
        asm volatile(
            // s = s + (ac + bd) + j(bc - ad)
            "vfdotpex.s.h  %[as],  %[ab], %[cd];"
            "pv.shuffle2.h %[ndc], %[cd], %[shuffle_mask];"
            "xor %[ndc], %[neg_mask], %[ndc];"
            "vfdotpex.s.h  %[bs],  %[ab], %[ndc];"
            : [as] "+&r"(as), [bs] "+&r"(bs), [ndc] "+r"(ndc)
            : [ab] "r"(ab), [cd] "r"(cd), [neg_mask] "r"(neg_mask),
              [shuffle_mask] "r"(shuffle_mask)
            :);
      }
      as = (ap_f32 - as) / diag_f32;
      bs = (bp_f32 - bs) / diag_f32;
      asm volatile("vfcpka.h.s %0, %1, %2;" : "=r"(asbs) : "r"(as), "r"(bs) :);
      (*(v2h *)&pL[2U * (i * offset + j)]) = asbs;
    }
  }
  return;
}

#endif
