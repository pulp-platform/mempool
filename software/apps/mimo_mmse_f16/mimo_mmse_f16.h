// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_hermitian_f16s(__fp16 *pH, __fp16 *pG, __fp16 *sigma, const uint32_t n_rx, const uint32_t n_tx);
void mempool_cholesky_f16s(__fp16 *pSrc, __fp16 *pL, const uint32_t n);
void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n);
void mempool_Lttrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n);

/* Computes the Hermitian matrix G = (H'*H + sigma^2I) */
void mempool_hermitian_f16s(__fp16 *pH, __fp16 *pG, __fp16 *sigma, const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j, k;
  __fp16 a;
  __fp16 b;
  __fp16 c0, c1, c2, c3;
  __fp16 d0, d1, d2, d3;
  __fp16 as0, as1, as2, as3;
  __fp16 bs0, bs1, bs2, bs3;
  for (i = 0; i < n_tx; i++) {
    j = 0;
    do {
      // Initialize the real part of sums
      as0 = (__fp16)0.0f;
      as1 = (__fp16)0.0f;
      as2 = (__fp16)0.0f;
      as3 = (__fp16)0.0f;
      // Initialize the imag part of sums
      bs0 = (__fp16)0.0f;
      bs1 = (__fp16)0.0f;
      bs2 = (__fp16)0.0f;
      bs3 = (__fp16)0.0f;
      // Inner Loop
      for (k = 0; k < n_rx; k++) {
        // inputs from matrix H_h
        a = pH[2U * (k * n_tx + i)];
        b = pH[2U * (k * n_tx + i) + 1U];
        // inputs from matrix H
        c0 = pH[2U * (k * n_tx + j)];
        c1 = pH[2U * (k * n_tx + j + 1U)];
        c2 = pH[2U * (k * n_tx + j + 2U)];
        c3 = pH[2U * (k * n_tx + j + 3U)];
        d0 = pH[2U * (k * n_tx + j) + 1U];
        d1 = pH[2U * (k * n_tx + j + 1U) + 1U];
        d2 = pH[2U * (k * n_tx + j + 2U) + 1U];
        d3 = pH[2U * (k * n_tx + j + 3U) + 1U];
        // dotproducts (ac + bd) + j (ad - bc)
        asm volatile (
          // a * c
          "fmadd.h  %[as0], %[a], %[c0], %[as0];"
          "fmadd.h  %[as1], %[a], %[c1], %[as1];"
          "fmadd.h  %[as2], %[a], %[c2], %[as2];"
          "fmadd.h  %[as3], %[a], %[c3], %[as3];"
          // a * d
          "fmadd.h  %[bs0], %[a], %[d0], %[bs0];"
          "fmadd.h  %[bs1], %[a], %[d3], %[bs1];"
          "fmadd.h  %[bs2], %[a], %[d2], %[bs2];"
          "fmadd.h  %[bs3], %[a], %[d3], %[bs3];"
          // b * d
          "fmadd.h  %[as0], %[b], %[d0], %[as0];"
          "fmadd.h  %[as1], %[b], %[d1], %[as1];"
          "fmadd.h  %[as2], %[b], %[d2], %[as2];"
          "fmadd.h  %[as3], %[b], %[d3], %[as3];"
          // - b * c
          "fnmsub.h %[bs0], %[b], %[c0], %[bs0];"
          "fnmsub.h %[bs1], %[b], %[c1], %[bs1];"
          "fnmsub.h %[bs2], %[b], %[c2], %[bs2];"
          "fnmsub.h %[bs3], %[b], %[c3], %[bs3];"
          : [as0] "+&r" (as0), [as1] "+&r" (as1), [as2] "+&r" (as2), [as3] "+&r" (as3),
            [bs0] "+&r" (bs0), [bs1] "+&r" (bs1), [bs2] "+&r" (bs2), [bs3] "+&r" (bs3)
          : [a] "r" (a), [b] "r" (b),
            [c0] "r" (c0), [c1] "r" (c1), [c2] "r" (c2), [c3] "r" (c3),
            [d0] "r" (d0), [d1] "r" (d1), [d2] "r" (d2), [d3] "r" (d3)
          :);
      }
      // Compute diagonal elements
      if (i == j) {
        asm volatile (
          "fadd.h  %[as0], %[as0], %[sigma];"
          : [as0] "+&r" (as0)
          : [sigma] "r" (sigma[i])
          :);
        bs0 = (__fp16)0.0f;
      }
      else if (i == (j + 1U)) {
        asm volatile (
          "fadd.h  %[as1], %[as1], %[sigma];"
          : [as1] "+&r" (as1)
          : [sigma] "r" (sigma[i])
          :);
        bs1 = (__fp16)0.0f;
      }
      else if (i == (j + 2U)) {
        asm volatile (
          "fadd.h  %[as2], %[as2], %[sigma];"
          : [as2] "+&r" (as2)
          : [sigma] "r" (sigma[i])
          :);
        bs2 = (__fp16)0.0f;
      }
      else if (i == (j + 3U)) {
        asm volatile (
          "fadd.h  %[as3], %[as3], %[sigma];"
          : [as3] "+&r" (as3)
          : [sigma] "r" (sigma[i])
          :);
        bs3 = (__fp16)0.0f;
      }
      // Store
      pG[2 * (i * n_tx + j)] = as0;
      pG[2 * (i * n_tx + j + 1U)] = as1;
      pG[2 * (i * n_tx + j + 2U)] = as2;
      pG[2 * (i * n_tx + j + 3U)] = as3;
      pG[2 * (i * n_tx + j) + 1U] = bs0;
      pG[2 * (i * n_tx + j + 1U) + 1U] = bs1;
      pG[2 * (i * n_tx + j + 2U) + 1U] = bs2;
      pG[2 * (i * n_tx + j + 3U) + 1U] = bs3;
      j += 4;
    } while (j < (n_tx >> 2U));
  }
  return;
}

void mempool_MVP_conjtransp_f16s(__fp16 *pH, __fp16 *pb, __fp16 *py, const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j;
  __fp16 a0, a1, a2, a3;
  __fp16 b0, b1, b2, b3;
  __fp16 c, d;
  __fp16 as0, as1, as2, as3;
  __fp16 bs0, bs1, bs2, bs3;

  i = 0;
  do {
    // Initialize the real part of sums
    as0 = (__fp16)0.0f;
    as1 = (__fp16)0.0f;
    as2 = (__fp16)0.0f;
    as3 = (__fp16)0.0f;
    // Initialize the imag part of sums
    bs0 = (__fp16)0.0f;
    bs1 = (__fp16)0.0f;
    bs2 = (__fp16)0.0f;
    bs3 = (__fp16)0.0f;
    for (j = 0; j < n_rx; j++) {
      // inputs from matrix H_h
      a0 = pH[2U * (j * n_tx + i)];
      a1 = pH[2U * (j * n_tx + i + 1U)];
      a2 = pH[2U * (j * n_tx + i + 2U)];
      a3 = pH[2U * (j * n_tx + i + 3U)];
      // inputs from matrix H_h
      b0 = pH[2U * (j * n_tx + i) + 1U];
      b1 = pH[2U * (j * n_tx + i + 1U) + 1U];
      b2 = pH[2U * (j * n_tx + i + 2U) + 1U];
      b3 = pH[2U * (j * n_tx + i + 3U) + 1U];
      // inputs from b
      c = pb[2U * j];
      d = pb[2U * j + 1U];
      asm volatile (
        // a * c
        "fmadd.h  %[as0], %[a0], %[c], %[as0];"
        "fmadd.h  %[as1], %[a1], %[c], %[as1];"
        "fmadd.h  %[as2], %[a2], %[c], %[as2];"
        "fmadd.h  %[as3], %[a3], %[c], %[as3];"
        // a * d
        "fmadd.h  %[bs0], %[a0], %[d], %[bs0];"
        "fmadd.h  %[bs1], %[a1], %[d], %[bs1];"
        "fmadd.h  %[bs2], %[a2], %[d], %[bs2];"
        "fmadd.h  %[bs3], %[a3], %[d], %[bs3];"
        // b * d
        "fmadd.h  %[as0], %[b0], %[d], %[as0];"
        "fmadd.h  %[as1], %[b1], %[d], %[as1];"
        "fmadd.h  %[as2], %[b2], %[d], %[as2];"
        "fmadd.h  %[as3], %[b3], %[d], %[as3];"
        // - b * c
        "fnmsub.h %[bs0], %[b0], %[c], %[bs0];"
        "fnmsub.h %[bs1], %[b1], %[c], %[bs1];"
        "fnmsub.h %[bs2], %[b2], %[c], %[bs2];"
        "fnmsub.h %[bs3], %[b3], %[c], %[bs3];"
        : [as0] "+&r" (as0), [as1] "+&r" (as1), [as2] "+&r" (as2), [as3] "+&r" (as3),
          [bs0] "+&r" (bs0), [bs1] "+&r" (bs1), [bs2] "+&r" (bs2), [bs3] "+&r" (bs3)
        : [c] "r" (c), [d] "r" (d),
          [a0] "r" (a0), [a1] "r" (a1), [a2] "r" (a2), [a3] "r" (a3),
          [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3)
        :);
    }
    // Store
    py[2U * i] = as0;
    py[2U * (i + 1U)] = as1;
    py[2U * (i + 2U)] = as2;
    py[2U * (i + 3U)] = as3;
    py[2U * i + 1U] = bs0;
    py[2U * (i + 1U) + 1U] = bs1;
    py[2U * (i + 2U) + 1U] = bs2;
    py[2U * (i + 3U) + 1U] = bs3;
    i += 4;
  } while (i < (n_tx >> 4U));
  return;
}

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
    diag = pL[2 * (i * n + i)];
    as = (__fp16)in[2U * i];
    bs = (__fp16)in[2U * i + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * (i * n + j)];
      b = pL[2U * (i * n + j) + 1];
      c = x[2U * j];
      d = x[2U * j + 1];
      asm volatile (
        "fnmsub.h  %[as], %[a], %[c], %[as];"
        "fnmsub.h  %[bs], %[a], %[d], %[bs];"
        "fmadd.h   %[as], %[b], %[d], %[as];"
        "fnmsub.h  %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile (
      "fdiv.h %[ax], %[as], %[diag];"
      "fdiv.h %[bx], %[bs], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
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
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    diag = pL[2 * ((n - 1 - i) * n + (n - 1 - i))];
    as = (__fp16)in[2 * (n - i - 1)];
    bs = (__fp16)in[2 * (n - i - 1) + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * ((n - 1 - j) * n + (n - 1 - i))];
      b = pL[2U * ((n - 1 - j) * n + (n - 1 - i)) + 1];
      c = x[2U * (n - 1 - j)];
      d = x[2U * (n - 1 - j) + 1];
      asm volatile (
        "fnmsub.h  %[as], %[a], %[c], %[as];"
        "fnmsub.h  %[as], %[b], %[d], %[as];"
        "fnmsub.h  %[bs], %[a], %[d], %[bs];"
        "fmadd.h   %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile (
      "fdiv.h %[ax], %[as], %[diag];"
      "fdiv.h %[bx], %[bs], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
      :);
    x[2U * (n - i - 1)] = ax;
    x[2U * (n - i - 1) + 1] = bx;
  }
  return;
}

