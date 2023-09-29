// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

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
    ap = pSrc[j * NUM_BANKS + 2 * j];
    sum = (__fp16)0.0f;
    for (k = 0; k < j; k++) {
      a = pL[j * NUM_BANKS + 2 * k];
      b = pL[j * NUM_BANKS + 2 * k + 1];
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
    pL[j * NUM_BANKS + 2 * j] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[i * NUM_BANKS + 2 * j];
      bp = pSrc[i * NUM_BANKS + 2 * j + 1];
      // Diag
      diag = pL[j * NUM_BANKS + 2 * j];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = (__fp16)0.0f;
      bs = (__fp16)0.0f;
      for (k = 0; k < j; k++) {
        a = pL[i * NUM_BANKS + 2 * k];
        b = pL[i * NUM_BANKS + 2 * k + 1];
        c = pL[j * NUM_BANKS + 2 * k];
        d = pL[j * NUM_BANKS + 2 * k + 1];
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
      pL[i * NUM_BANKS + 2 * j] = ap;
      pL[i * NUM_BANKS + 2 * j + 1] = bp;
    }
  }
  return;
}
