// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cholesky_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n);
void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n);
void mempool_Lttrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n);

void mempool_cholesky_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n) {

  register __fp16 sum;
  __fp16 a, b;
  __fp16 c, d;
  __fp16 diag; // Diagonal element
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
        asm volatile(
          "fmadd.h %[sum], %[a], %[a], %[sum];"
          "fmadd.h %[sum], %[b], %[b], %[sum];"
          : [sum] "+&r" (sum)
          : [a] "r" (a), [b] "r" (b) :);
      }
      asm volatile(
        "fsub.h %[ap], %[ap], %[sum];"
        "fsqrt.h  %[ap], %[ap];"
        : [ap] "+&r" (ap) : [sum] "r" (sum) :);
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
          asm volatile (
            "fmadd.h %[as], %[a], %[c], %[as];"
            "fmadd.h %[as], %[b], %[d], %[as];"
            "fmadd.h %[bs], %[b], %[c], %[bs];"
            "fnmsub.h %[bs], %[a], %[d], %[bs];"
            : [as] "+&r" (as), [bs] "+&r" (bs)
            : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
            :);
        }
        asm volatile (
          "fsub.h %[ap], %[ap], %[as];"
          "fsub.h %[bp], %[bp], %[bs];"
          "fdiv.h %[ap], %[ap], %[diag];"
          "fdiv.h %[bp], %[bp], %[diag];"
          : [ap] "+&r" (ap), [bp] "+&r" (bp)
          : [diag] "r" (diag), [as] "r" (as), [bs] "r" (bs)
          :);
        pL[2U * (i * n + j)] = ap;
        pL[2U * (i * n + j) + 1] = bp;
      }

  }
  return;
}

void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ab, bb;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    as = (__fp16)0.0f;
    bs = (__fp16)0.0f;
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * (i * n + j)];
      b = pL[2U * (i * n + j) + 1];
      c = x[2U * j];
      d = x[2U * j + 1];
      asm volatile (
        "fmadd.h  %[as], %[a], %[c], %[as];"
        "fnmsub.h %[as], %[b], %[d], %[as];"
        "fmadd.h %[bs], %[a], %[d], %[bs];"
        "fmadd.h %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    diag = pL[2 * (i * n + i)];
    ab = in[2U * i];
    bb = in[2U * i + 1];
    asm volatile (
      "fsub.h %[ax], %[ab], %[as];"
      "fsub.h %[bx], %[bb], %[bs];"
      "fdiv.h %[ax], %[ax], %[diag];"
      "fdiv.h %[bx], %[bx], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [ab] "r" (ab), [bb] "r" (bb),
        [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
      :);
    x[2U * i] = ax;
    x[2U * i + 1] = bx;
  }
  return;
}

void mempool_Lttrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ab, bb;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    as = (__fp16)0.0f;
    bs = (__fp16)0.0f;
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * ((n - 1 - j) * n + (n - 1 - i))];
      b = pL[2U * ((n - 1 - j) * n + (n - 1 - i)) + 1];
      c = x[2U * (n - 1 - j)];
      d = x[2U * (n - 1 - j) + 1];
      asm volatile (
        "fmadd.h  %[as], %[a], %[c], %[as];"
        "fnmsub.h %[as], %[b], %[d], %[as];"
        "fmadd.h  %[bs], %[a], %[d], %[bs];"
        "fmadd.h  %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    diag = pL[2 * ((n - 1 - i) * n + (n - 1 - i))];
    ab = in[2 * (n - i - 1)];
    bb = in[2 * (n - i - 1) + 1];
    asm volatile (
      "fsub.h %[ax], %[ab], %[as];"
      "fsub.h %[bx], %[bb], %[bs];"
      "fdiv.h %[ax], %[ax], %[diag];"
      "fdiv.h %[bx], %[bx], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [ab] "r" (ab), [bb] "r" (bb),
        [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
      :);
    x[2U * (n - i - 1)] = ax;
    x[2U * (n - i - 1) + 1] = bx;
  }
  return;
}


