// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich


dump(results,1);

void mempool_hermitian_f32s(float *pH, float *pG, float *sigma, const uint32_t n_rx, const uint32_t n_tx);
void mempool_cholesky_f32s(float *pSrc, float *pL, const uint32_t n);
void mempool_Ltrisol_f32s(float *pL, float *in, float *x, const uint32_t n);
void mempool_Lttrisol_f32s(float *pL, float *in, float *x, const uint32_t n);

/* Computes the Hermitian matrix G = (H'*H + sigma^2I) */
void mempool_hermitian_f32s(float *pH, float *pG, float *sigma, const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j, k;
  float a, b;
  float c, d;
  float as, bs;

  for (i = 0; i < n_tx; i++) {
    for (j = 0; j < n_tx; j++) {
      as = 0.0f;
      bs = 0.0f;
      for (k = 0; k < n_rx; k++) {
        a = pH[2U * (k * n_tx + i)];
        b = pH[2U * (k * n_tx + i) + 1U];
        c = pH[2U * (k * n_tx + j)];
        d = pH[2U * (k * n_tx + j) + 1U];
        asm volatile (
          "fmadd.s %[as], %[a], %[c], %[as];"
          "fmadd.s %[as], %[b], %[d], %[as];"
          "fmadd.s %[bs], %[a], %[d], %[bs];"
          "fnmsub.s %[bs], %[b], %[c], %[bs];"
          : [as] "+&r" (as), [bs] "+&r" (bs)
          : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
          :);
      }
      if (i == j) {
        asm volatile (
          "fadd.s  %[as], %[as], %[sigma];"
          : [as] "+&r" (as), [bs] "+&r" (bs)
          : [a] "r" (a), [b] "r" (b), [sigma] "r" (sigma[i])
          :);
        bs = 0.0f;
      }
      pG[2U * (i * n_tx + j)] = as;
      pG[2U * (i * n_tx + j) + 1U] = bs;
    }
  }
  return;
}

void mempool_MVP_conjtransp_f32s(float *pH, float *pb, float *py, const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j;
  float a, b;
  float c, d;
  float as, bs;

  for (i = 0; i < n_tx; i++) {
    as = 0.0f;
    bs = 0.0f;
    for (j = 0; j < n_rx; j++) {
      a = pH[2U * (j * n_tx + i)];
      b = pH[2U * (j * n_tx + i) + 1U];
      c = pb[2U * j];
      d = pb[2U * j + 1U];
      asm volatile (
        "fmadd.s %[as], %[a], %[c], %[as];"
        "fmadd.s %[as], %[b], %[d], %[as];"
        "fmadd.s %[bs], %[a], %[d], %[bs];"
        "fnmsub.s %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    py[2U * i] = as;
    py[2U * i + 1U] = bs;
  }
  return;
}

void mempool_cholesky_f32s(float *pSrc, float *pL, const uint32_t n) {

  register float sum;
  float a, b;
  float c, d;
  float diag; // Diagonal element
  float ap, bp; // Pivot element
  float as, bs; // Sum element

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {

      // Elements on diagonal (input matrix is positive-definite)
      ap = pSrc[2U * (j * n + j)];
      sum = 0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (j * n + k)];
        b = pL[2U * (j * n + k) + 1];
        asm volatile(
          "fmadd.s %[sum], %[a], %[a], %[sum];"
          "fmadd.s %[sum], %[b], %[b], %[sum];"
          : [sum] "+&r" (sum)
          : [a] "r" (a), [b] "r" (b) :);
      }
      asm volatile(
        "fsub.s %[ap], %[ap], %[sum];"
        "fsqrt.s  %[ap], %[ap];"
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
        as = 0.0f;
        bs = 0.0f;
        for (k = 0; k < j; k++) {
          a = pL[2U * (i * n + k)];
          b = pL[2U * (i * n + k) + 1];
          c = pL[2U * (j * n + k)];
          d = pL[2U * (j * n + k) + 1];
          asm volatile (
            "fmadd.s %[as], %[a], %[c], %[as];"
            "fmadd.s %[as], %[b], %[d], %[as];"
            "fmadd.s %[bs], %[b], %[c], %[bs];"
            "fnmsub.s %[bs], %[a], %[d], %[bs];"
            : [as] "+&r" (as), [bs] "+&r" (bs)
            : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
            :);
        }
        asm volatile (
          "fsub.s %[ap], %[ap], %[as];"
          "fsub.s %[bp], %[bp], %[bs];"
          "fdiv.s %[ap], %[ap], %[diag];"
          "fdiv.s %[bp], %[bp], %[diag];"
          : [ap] "+&r" (ap), [bp] "+&r" (bp)
          : [diag] "r" (diag), [as] "r" (as), [bs] "r" (bs)
          :);
        pL[2U * (i * n + j)] = ap;
        pL[2U * (i * n + j) + 1] = bp;
      }

  }
  return;
}


void mempool_Ltrisol_f32s(float *pL, float *in, float *x, const uint32_t n) {

  uint32_t i, j;
  float a, b;
  float c, d;

  float as, bs;
  float ab, bb;
  float ax, bx;
  float diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    as = 0.0f;
    bs = 0.0f;
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * (i * n + j)];
      b = pL[2U * (i * n + j) + 1];
      c = x[2U * j];
      d = x[2U * j + 1];
      asm volatile (
        "fmadd.s  %[as], %[a], %[c], %[as];"
        "fnmsub.s %[as], %[b], %[d], %[as];"
        "fmadd.s %[bs], %[a], %[d], %[bs];"
        "fmadd.s %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    diag = pL[2 * (i * n + i)];
    ab = in[2U * i];
    bb = in[2U * i + 1];
    asm volatile (
      "fsub.s %[ax], %[ab], %[as];"
      "fsub.s %[bx], %[bb], %[bs];"
      "fdiv.s %[ax], %[ax], %[diag];"
      "fdiv.s %[bx], %[bx], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [ab] "r" (ab), [bb] "r" (bb),
        [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
      :);
    x[2U * i] = ax;
    x[2U * i + 1] = bx;
  }
  return;
}

void mempool_Lttrisol_f32s(float *pL, float *in, float *x, const uint32_t n) {

  uint32_t i, j;
  float a, b;
  float c, d;

  float as, bs;
  float ab, bb;
  float ax, bx;
  float diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    as = 0.0f;
    bs = 0.0f;
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * ((n - 1 - j) * n + (n - 1 - i))];
      b = pL[2U * ((n - 1 - j) * n + (n - 1 - i)) + 1];
      c = x[2U * (n - 1 - j)];
      d = x[2U * (n - 1 - j) + 1];
      asm volatile (
        "fmadd.s  %[as], %[a], %[c], %[as];"
        "fnmsub.s %[as], %[b], %[d], %[as];"
        "fmadd.s  %[bs], %[a], %[d], %[bs];"
        "fmadd.s  %[bs], %[b], %[c], %[bs];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
        :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    diag = pL[2 * ((n - 1 - i) * n + (n - 1 - i))];
    ab = in[2 * (n - i - 1)];
    bb = in[2 * (n - i - 1) + 1];
    asm volatile (
      "fsub.s %[ax], %[ab], %[as];"
      "fsub.s %[bx], %[bb], %[bs];"
      "fdiv.s %[ax], %[ax], %[diag];"
      "fdiv.s %[bx], %[bx], %[diag];"
      : [ax] "+&r" (ax), [bx] "+&r" (bx)
      : [ab] "r" (ab), [bb] "r" (bb),
        [as] "r" (as), [bs] "r" (bs), [diag] "r" (diag)
      :);
    x[2U * (n - i - 1)] = ax;
    x[2U * (n - i - 1) + 1] = bx;
  }
  return;
}

