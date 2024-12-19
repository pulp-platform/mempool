// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifdef __XDIVSQRT

/**
  @brief         Cholesky decomposition with Crout algorithm.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_f32s(float *pSrc, float *pL, const uint32_t n,
                           const uint32_t folded) {

  register float sum;
  float a, b;
  float c, d;
  float diag;   // Diagonal element
  float ap, bp; // Pivot element
  float as, bs; // Sum element
  uint32_t i, j, k;
  const uint32_t offset = folded ? NUM_BANKS : n;

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * offset + j)];
    sum = 0.0f;
    for (k = 0; k < j; k++) {
      a = pL[2U * (j * offset + k)];
      b = pL[2U * (j * offset + k) + 1];
      asm volatile("fmadd.s %[sum], %[a], %[a], %[sum];"
                   "fmadd.s %[sum], %[b], %[b], %[sum];"
                   : [sum] "+&r"(sum)
                   : [a] "r"(a), [b] "r"(b)
                   :);
    }
    asm volatile("fsub.s %[ap], %[ap], %[sum];"
                 "fsqrt.s  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
    pL[2U * (j * n + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * offset + j)];
      bp = pSrc[2U * (i * offset + j) + 1];
      // Diag
      diag = pL[2U * (j * offset + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = 0.0f;
      bs = 0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (i * offset + k)];
        b = pL[2U * (i * offset + k) + 1];
        c = pL[2U * (j * offset + k)];
        d = pL[2U * (j * offset + k) + 1];
        asm volatile("fmadd.s %[as], %[a], %[c], %[as];"
                     "fmadd.s %[as], %[b], %[d], %[as];"
                     "fmadd.s %[bs], %[b], %[c], %[bs];"
                     "fnmsub.s %[bs], %[a], %[d], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
      asm volatile("fsub.s %[ap], %[ap], %[as];"
                   "fsub.s %[bp], %[bp], %[bs];"
                   "fdiv.s %[ap], %[ap], %[diag];"
                   "fdiv.s %[bp], %[bp], %[diag];"
                   : [ap] "+&r"(ap), [bp] "+&r"(bp)
                   : [diag] "r"(diag), [as] "r"(as), [bs] "r"(bs)
                   :);
      pL[2U * (i * offset + j)] = ap;
      pL[2U * (i * offset + j) + 1] = bp;
    }
  }
  return;
}

#else

#error "ERROR: f32 MMSE functions available only for __XDIVSQRT."

#endif
