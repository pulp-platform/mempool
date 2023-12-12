// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich
// Author: Bowen Wang, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

/**
  @brief         Cholesky decomposition with Crout algorithm.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n) {

  register __fp16 sum;
  __fp16 a, b;
  __fp16 c, d;
  __fp16 diag;   // Diagonal element
  __fp16 ap, bp; // Pivot element
  __fp16 as, bs; // Sum element

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * n + j)];
    sum = (__fp16)0.0f;
    for (k = 0; k < j; k++) {
      a = pL[2U * (j * n + k)];
      b = pL[2U * (j * n + k) + 1];
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
    pL[2U * (j * n + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * n + j)];
      bp = pSrc[2U * (i * n + j) + 1];
      // Diag
      diag = pL[2U * (j * n + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (__fp16)0.0f;
      bs = (__fp16)0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (i * n + k)];
        b = pL[2U * (i * n + k) + 1];
        c = pL[2U * (j * n + k)];
        d = pL[2U * (j * n + k) + 1];
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
      pL[2U * (i * n + j)] = ap;
      pL[2U * (i * n + j) + 1] = bp;
    }
  }
  return;
}

/**
  @brief         Cholesky decomposition with Crout algorithm.
  Output data is folded to the core's local memory.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_folded_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n) {

  register __fp16 sum;
  __fp16 a, b;
  __fp16 c, d;
  __fp16 diag;   // Diagonal element
  __fp16 ap, bp; // Pivot element
  __fp16 as, bs; // Sum element

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * N_BANKS + j)];
    sum = (__fp16)0.0f;
    for (k = 0; k < j; k++) {
      a = pL[2U * (j * N_BANKS + k)];
      b = pL[2U * (j * N_BANKS + k) + 1];
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
    pL[2U * (j * N_BANKS + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * N_BANKS + j)];
      bp = pSrc[2U * (i * N_BANKS + j) + 1];
      // Diag
      diag = pL[2U * (j * N_BANKS + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (__fp16)0.0f;
      bs = (__fp16)0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (i * N_BANKS + k)];
        b = pL[2U * (i * N_BANKS + k) + 1];
        c = pL[2U * (j * N_BANKS + k)];
        d = pL[2U * (j * N_BANKS + k) + 1];
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
      pL[2U * (i * N_BANKS + j)] = ap;
      pL[2U * (i * N_BANKS + j) + 1] = bp;
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
void mempool_cholesky_f16vecs(__fp16 *pSrc, __fp16 *pL, const uint32_t n) {

  float sum;   // register float sum
  __fp16 diag; // Diagonal element
  __fp16 ap;

  float as, bs;
  v2h abp, ab, cd, ndc;
  v2h vec_sum;
  v2h vec_diag;

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * n + j)];
    sum = (float)0.0f;
    for (k = 0; k < j; k++) {
      ab = (*(v2h *)&pL[2U * (j * n + k)]);
      asm volatile("vfdotpex.s.h %[sum], %[ab],  %[ab];"
                   : [sum] "+&r"(sum)
                   : [ab] "r"(ab)
                   :);
    }
    asm volatile("fcvt.h.s %[sum], %[sum];"
                 "fsub.h %[ap], %[ap], %[sum];"
                 "fsqrt.h  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
    pL[2U * (j * n + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      abp = (*(v2h *)&pSrc[2U * (i * n + j)]);
      // Diag
      diag = pL[2U * (j * n + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (float)0.0f;
      bs = (float)0.0f;
      for (k = 0; k < j; k++) {
        ab = (*(v2h *)&pL[2U * (i * n + k)]);
        cd = (*(v2h *)&pL[2U * (j * n + k)]);
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
      asm volatile("vfcpka.h.s %[vec_sum], %[as], %[bs];"
                   "pv.pack.h %[vec_diag], %[diag], %[diag];"
                   "vfsub.h %[abp], %[abp], %[vec_sum];"
                   "vfdiv.h %[abp], %[abp], %[vec_diag];"
                   : [abp] "+&r"(abp), [vec_sum] "+&r"(vec_sum),
                     [vec_diag] "+&r"(vec_diag)
                   : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                   :);
      (*(v2h *)&pL[2U * (i * n + j)]) = abp;
    }
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
  v2h vec_diag;

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * n + j)];
    sum = (float)0.0f;
    for (k = 0; k < j; k++) {
      ab1 = (*(v2h *)&pL[2U * (j * n + k)]);
      asm volatile("vfdotpex.s.h %[sum], %[ab1],  %[ab1];"
                   : [sum] "+&r"(sum)
                   : [ab1] "r"(ab1)
                   :);
    }

    asm volatile("vfcpka.h.s %[sum], %[sum], %[sum];"
                 "fsub.h %[ap], %[ap], %[sum];"
                 "fsqrt.h  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
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

      asm volatile("vfcpka.h.s %[vec_diag], %[as1], %[bs1];"
                   "vfsub.h %[abp], %[abp], %[vec_diag];"
                   "pv.pack.h %[vec_diag], %[diag], %[diag];"
                   "vfdiv.h %[abp], %[abp], %[vec_diag];"
                   : [abp] "+&r"(abp), [vec_diag] "+&r"(vec_diag)
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
      asm volatile("vfcpka.h.s %[vec_diag], %[as1], %[bs1];"
                   "vfcpka.h.s %[vec_diag], %[as2], %[bs2];"
                   "vfcpka.h.s %[vec_diag], %[as3], %[bs3];"
                   "vfcpka.h.s %[vec_diag], %[as4], %[bs4];"

                   "vfsub.h %[abp1], %[abp1], %[vec_diag];"
                   "vfsub.h %[abp2], %[abp2], %[vec_diag];"
                   "vfsub.h %[abp3], %[abp3], %[vec_diag];"
                   "vfsub.h %[abp4], %[abp4], %[vec_diag];"

                   "pv.pack.h %[vec_diag], %[diag], %[diag];"
                   "vfdiv.h %[abp1], %[abp1], %[vec_diag];"
                   "vfdiv.h %[abp2], %[abp2], %[vec_diag];"
                   "vfdiv.h %[abp3], %[abp3], %[vec_diag];"
                   "vfdiv.h %[abp4], %[abp4], %[vec_diag];"

                   "andi %[as1], %[as1], 0;"
                   "andi %[bs1], %[as1], 0;"
                   "andi %[as2], %[as1], 0;"
                   "andi %[bs2], %[as1], 0;"
                   "andi %[as3], %[as1], 0;"
                   "andi %[bs3], %[as1], 0;"
                   "andi %[as4], %[as1], 0;"
                   "andi %[bs4], %[as1], 0;"

                   : [abp1] "+&r"(abp1), [abp2] "+&r"(abp2), [abp3] "+&r"(abp3),
                     [abp4] "+&r"(abp4), [vec_diag] "+&r"(vec_diag),
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
