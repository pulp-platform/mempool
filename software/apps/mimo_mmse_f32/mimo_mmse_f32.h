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
  float a;
  float b;
  float c0, c1, c2, c3;
  float d0, d1, d2, d3;
  float as0, as1, as2, as3;
  float bs0, bs1, bs2, bs3;
  for (i = 0; i < n_tx; i++) {
    j = 0;
    do {
      // Initialize the real part of sums
      as0 = 0.0f;
      as1 = 0.0f;
      as2 = 0.0f;
      as3 = 0.0f;
      // Initialize the imag part of sums
      bs0 = 0.0f;
      bs1 = 0.0f;
      bs2 = 0.0f;
      bs3 = 0.0f;
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
          "fmadd.s  %[as0], %[a], %[c0], %[as0];"
          "fmadd.s  %[as1], %[a], %[c1], %[as1];"
          "fmadd.s  %[as2], %[a], %[c2], %[as2];"
          "fmadd.s  %[as3], %[a], %[c3], %[as3];"
          // a * d
          "fmadd.s  %[bs0], %[a], %[d0], %[bs0];"
          "fmadd.s  %[bs1], %[a], %[d1], %[bs1];"
          "fmadd.s  %[bs2], %[a], %[d2], %[bs2];"
          "fmadd.s  %[bs3], %[a], %[d3], %[bs3];"
          // b * d
          "fmadd.s  %[as0], %[b], %[d0], %[as0];"
          "fmadd.s  %[as1], %[b], %[d1], %[as1];"
          "fmadd.s  %[as2], %[b], %[d2], %[as2];"
          "fmadd.s  %[as3], %[b], %[d3], %[as3];"
          // - b * c
          "fnmsub.s %[bs0], %[b], %[c0], %[bs0];"
          "fnmsub.s %[bs1], %[b], %[c1], %[bs1];"
          "fnmsub.s %[bs2], %[b], %[c2], %[bs2];"
          "fnmsub.s %[bs3], %[b], %[c3], %[bs3];"
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
          "fadd.s  %[as0], %[as0], %[sigma];"
          : [as0] "+&r" (as0)
          : [sigma] "r" (sigma[i])
          :);
        bs0 = 0.0f;
      }
      else if (i == (j + 1U)) {
        asm volatile (
          "fadd.s  %[as1], %[as1], %[sigma];"
          : [as1] "+&r" (as1)
          : [sigma] "r" (sigma[i])
          :);
        bs1 = 0.0f;
      }
      else if (i == (j + 2U)) {
        asm volatile (
          "fadd.s  %[as2], %[as2], %[sigma];"
          : [as2] "+&r" (as2)
          : [sigma] "r" (sigma[i])
          :);
        bs2 = 0.0f;
      }
      else if (i == (j + 3U)) {
        asm volatile (
          "fadd.s  %[as3], %[as3], %[sigma];"
          : [as3] "+&r" (as3)
          : [sigma] "r" (sigma[i])
          :);
        bs3 = 0.0f;
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

void mempool_MVP_conjtransp_f32s(float *pH, float *pb, float *py, const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j;
  float a0, a1, a2, a3;
  float b0, b1, b2, b3;
  float c, d;
  float as0, as1, as2, as3;
  float bs0, bs1, bs2, bs3;

  i = 0;
  do {
    // Initialize the real part of sums
    as0 = 0.0f;
    as1 = 0.0f;
    as2 = 0.0f;
    as3 = 0.0f;
    // Initialize the imag part of sums
    bs0 = 0.0f;
    bs1 = 0.0f;
    bs2 = 0.0f;
    bs3 = 0.0f;
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
        "fmadd.s  %[as0], %[a0], %[c], %[as0];"
        "fmadd.s  %[as1], %[a1], %[c], %[as1];"
        "fmadd.s  %[as2], %[a2], %[c], %[as2];"
        "fmadd.s  %[as3], %[a3], %[c], %[as3];"
        // a * d
        "fmadd.s  %[bs0], %[a0], %[d], %[bs0];"
        "fmadd.s  %[bs1], %[a1], %[d], %[bs1];"
        "fmadd.s  %[bs2], %[a2], %[d], %[bs2];"
        "fmadd.s  %[bs3], %[a3], %[d], %[bs3];"
        // b * d
        "fmadd.s  %[as0], %[b0], %[d], %[as0];"
        "fmadd.s  %[as1], %[b1], %[d], %[as1];"
        "fmadd.s  %[as2], %[b2], %[d], %[as2];"
        "fmadd.s  %[as3], %[b3], %[d], %[as3];"
        // - b * c
        "fnmsub.s %[bs0], %[b0], %[c], %[bs0];"
        "fnmsub.s %[bs1], %[b1], %[c], %[bs1];"
        "fnmsub.s %[bs2], %[b2], %[c], %[bs2];"
        "fnmsub.s %[bs3], %[b3], %[c], %[bs3];"
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

void mempool_jacobi_f32s(float* pA, float* in, float* x, float tol, const uint32_t n, const uint32_t max_iter)
{

  uint32_t i, j, k;
  float diff, error, den;
  float as, bs;
  float ab, bb;
  float a, b;
  float c, d;

  for (k = 0; k < max_iter; k++) {
    // Initialize the diff variable
    diff = 0.0f;

    /* COMPUTE THE SUM */
    for (i = 0; i < n; i++) {
      as = 0.0f;
      bs = 0.0f;
      ab = in[2U * i];
      bb = in[2U * i + 1];
      den = pA[2U * (i * n + i)];
      // Compute the output
      for (j = 0; j < n; j++) {
        if (j != i) {
          a = pA[2U * (i * n + j)];
          b = pA[2U * (i * n + j) + 1U];
          c = x[2U * j];
          d = x[2U * j + 1U];
          // (ac - bd) + j * (ad + bc)
          asm volatile (
            "fmadd.s  %[as], %[a], %[c], %[as];"
            "fnmsub.s %[as], %[b], %[d], %[as];"
            "fmadd.s  %[bs], %[a], %[d], %[bs];"
            "fmadd.s  %[bs], %[b], %[c], %[bs];"
            : [as] "+&r" (as), [bs] "+&r" (bs)
            : [a] "r" (a), [b] "r" (b), [c] "r" (c), [d] "r" (d)
            :);
        }
      }

      /* COMPUTE THE NEW DATA */
      asm volatile (
        // subtract the sum from the input vector
        "fsub.s %[as], %[ab], %[as];"
        "fsub.s %[bs], %[bb], %[bs];"
        // divide the result by the pivot
        "fdiv.s    %[as], %[as], %[den];"
        "fdiv.s    %[bs], %[bs], %[den];"
        : [as] "+&r" (as), [bs] "+&r" (bs)
        : [ab] "r" (ab), [bb] "r" (bb), [den] "r" (den)
        :);

      /* COMPUTE THE DIFFERENCE */
      // Load the previous result
      a = x[2U * i];
      b = x[2U * i + 1];
      // Compute diff
      asm volatile (
        "fsub.s %[a], %[a], %[as];"
        "fsub.s %[b], %[b], %[bs];"
        : [a] "+&r" (a), [b] "+&r" (b)
        : [as] "r" (as), [bs] "r" (bs)
        :);
      a = (a > 0.0f) ? a : (-a);
      b = (b > 0.0f) ? b : (-b);
      asm volatile (
        "fadd.s %[diff], %[a], %[diff];"
        "fadd.s %[diff], %[b], %[diff];"
        : [diff] "+&r" (diff)
        : [a] "r" (a), [b] "r" (b)
        :);

      /* STORE THE RESULT */
      x[2U * i] = as;
      x[2U * i + 1U] = bs;

    }
    /* COMPUTE THE ERROR */
    error = diff / (2.0f * (float)n);
    if (error < tol){
      break;
    }
  }
  return;
}

