// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

/**
  @brief         Computes the Hermitian matrix G = (H'*H + pS^2I).
  @param[in]     pH     points to input matrix
  @param[in]     pG     points to output matrix
  @param[in]     pS     points to the noise vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @param[in]     folded controls if output is folded
  @param[in]     zf     controls if the zero forcing is used
  @return        none
*/
void mempool_hermitian_f32s(float *pH, float *pG, float *pS,
                            const uint32_t n_rx, const uint32_t n_tx,
                            const uint32_t folded, const uint32_t zf) {

  uint32_t i, j, k;
  float a;
  float b;
  float c0, c1, c2, c3;
  float d0, d1, d2, d3;
  float as0, as1, as2, as3;
  float bs0, bs1, bs2, bs3;
  for (i = 0; i < n_tx; i++) {
    for (j = 0; j < n_tx; j += 4) {
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
        asm volatile(
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
            : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
              [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
              [bs2] "+&r"(bs2), [bs3] "+&r"(bs3)
            : [a] "r"(a), [b] "r"(b), [c0] "r"(c0), [c1] "r"(c1), [c2] "r"(c2),
              [c3] "r"(c3), [d0] "r"(d0), [d1] "r"(d1), [d2] "r"(d2),
              [d3] "r"(d3)
            :);
      }
      if (zf == 0) {
        // Compute diagonal elements
        if (i == j) {
          asm volatile("fadd.s  %[as0], %[as0], %[pS];"
                       : [as0] "+&r"(as0)
                       : [pS] "r"(pS[i])
                       :);
          bs0 = 0.0f;
        } else if (i == (j + 1U)) {
          asm volatile("fadd.s  %[as1], %[as1], %[pS];"
                       : [as1] "+&r"(as1)
                       : [pS] "r"(pS[i])
                       :);
          bs1 = 0.0f;
        } else if (i == (j + 2U)) {
          asm volatile("fadd.s  %[as2], %[as2], %[pS];"
                       : [as2] "+&r"(as2)
                       : [pS] "r"(pS[i])
                       :);
          bs2 = 0.0f;
        } else if (i == (j + 3U)) {
          asm volatile("fadd.s  %[as3], %[as3], %[pS];"
                       : [as3] "+&r"(as3)
                       : [pS] "r"(pS[i])
                       :);
          bs3 = 0.0f;
        }
      }
      if (!folded) {
        // Store
        pG[2 * (i * n_tx + j)] = as0;
        pG[2 * (i * n_tx + j + 1U)] = as1;
        pG[2 * (i * n_tx + j + 2U)] = as2;
        pG[2 * (i * n_tx + j + 3U)] = as3;
        pG[2 * (i * n_tx + j) + 1U] = bs0;
        pG[2 * (i * n_tx + j + 1U) + 1U] = bs1;
        pG[2 * (i * n_tx + j + 2U) + 1U] = bs2;
        pG[2 * (i * n_tx + j + 3U) + 1U] = bs3;
      } else {
        // Store
        uint32_t addr = i * ((n_tx / 2) * N_BANKS) + (j / 4) * (2 * N_BANKS);
        pG[addr] = as0;
        pG[addr + 1U] = bs0;
        pG[addr + 2U] = as1;
        pG[addr + 3U] = bs1;
        pG[addr + N_BANKS] = as2;
        pG[addr + N_BANKS + 1U] = bs2;
        pG[addr + N_BANKS + 2U] = as3;
        pG[addr + N_BANKS + 3U] = bs3;
      }
    }
  }
  return;
}

/**
  @brief         Computes the matrix-vector product y = H' * x.
  @param[in]     pH     points to input matrix
  @param[in]     pb     points to input vector
  @param[in]     py     points to output vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @param[in]     folded controls if output is folded
  @return        none
*/
void mempool_MVP_conjtransp_f32s(float *pH, float *px, float *py,
                                 const uint32_t n_rx, const uint32_t n_tx,
                                 const uint32_t folded) {

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
      c = px[2U * j];
      d = px[2U * j + 1U];
      asm volatile(
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
          : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
            [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
            [bs2] "+&r"(bs2), [bs3] "+&r"(bs3)
          : [c] "r"(c), [d] "r"(d), [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2),
            [a3] "r"(a3), [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3)
          :);
    }
    if (!folded) {
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
    } else {
      // Store
      uint32_t addr = (i / 4) * 2 * N_BANKS;
      py[addr] = as0;
      py[addr + 1U] = bs0;
      py[addr + 2U] = as1;
      py[addr + 3U] = bs1;
      py[addr + N_BANKS] = as2;
      py[addr + N_BANKS + 1U] = bs2;
      py[addr + N_BANKS + 2U] = as3;
      py[addr + N_BANKS + 3U] = bs3;
      i += 4;
    }
  } while (i < n_tx);
  return;
}

/**
  @brief         Inverts a system using the Jacobi method
  @param[in]     pA     points to input matrix
  @param[in]     py     points to the known vector
  @param[in]     px     points to the unknowns vector
  @param[in]     n      dimension of the system
  @param[in]     tol    tolerance on the result
  @param[in]     max_iter max number of iterations
  @return        none
*/
void mempool_jacobi_f32s(float *pA, float *in, float *px, const uint32_t n,
                         const float tol, const uint32_t max_iter) {
  uint32_t i, j, k;
  float error;
  float register diff, den;
  float register as0, as1;
  float register bs0, bs1;
  float a0, a1;
  float b0, b1;
  float c0, c1;
  float d0, d1;
  for (k = 0; k < max_iter; k++) {

    // Initialize the diff variable
    diff = 0.0f;

    /* COMPUTE THE SUM */
    for (i = 0; i < n; i++) {

      den = pA[2U * (i * n + i)];
      as0 = in[2U * i];
      bs0 = in[2U * i + 1];
      as1 = 0.0f;
      bs1 = 0.0f;
      asm volatile(
          // divide the result by the pivot
          "fdiv.s    %[den], %[imm], %[den];"
          : [den] "+&r"(den)
          : [imm] "r"((uint32_t)0x3F800000)
          :);

      /* COMPUTE OUTPUT */
      for (j = 0U; j < n; j += 2) {
        if (i == j) {
          a0 = pA[2U * (i * n + j + 1U)];
          b0 = pA[2U * (i * n + j + 1U) + 1U];
          c0 = px[2U * (j + 1U)];
          d0 = px[2U * (j + 1U) + 1U];
          // (ac - bd) + j * (ad + bc)
          asm volatile("fnmsub.s  %[as0], %[a0], %[c0], %[as0];"
                       "fnmsub.s  %[bs0], %[b0], %[c0], %[bs0];"
                       "fmadd.s   %[as0], %[b0], %[d0], %[as0];"
                       "fnmsub.s  %[bs0], %[a0], %[d0], %[bs0];"
                       : [as0] "+&r"(as0), [bs0] "+&r"(bs0)
                       : [a0] "r"(a0), [b0] "r"(b0), [c0] "r"(c0), [d0] "r"(d0)
                       :);
        } else if (i == (j + 1U)) {
          a0 = pA[2U * (i * n + j)];
          b0 = pA[2U * (i * n + j) + 1U];
          c0 = px[2U * j];
          d0 = px[2U * j + 1U];
          // (ac - bd) + j * (ad + bc)
          asm volatile("fnmsub.s  %[as0], %[a0], %[c0], %[as0];"
                       "fnmsub.s  %[bs0], %[b0], %[c0], %[bs0];"
                       "fmadd.s   %[as0], %[b0], %[d0], %[as0];"
                       "fnmsub.s  %[bs0], %[a0], %[d0], %[bs0];"
                       : [as0] "+&r"(as0), [bs0] "+&r"(bs0)
                       : [a0] "r"(a0), [b0] "r"(b0), [c0] "r"(c0), [d0] "r"(d0)
                       :);
        } else {
          a0 = pA[2U * (i * n + j)];
          a1 = pA[2U * (i * n + j + 1U)];
          b0 = pA[2U * (i * n + j) + 1U];
          b1 = pA[2U * (i * n + j + 1U) + 1U];
          c0 = px[2U * j];
          c1 = px[2U * (j + 1U)];
          d0 = px[2U * j + 1U];
          d1 = px[2U * (j + 1U) + 1U];
          // (ac - bd) + j * (ad + bc)
          asm volatile("fnmsub.s  %[as0], %[a0], %[c0], %[as0];"
                       "fnmsub.s  %[as1], %[a1], %[c1], %[as1];"
                       "fnmsub.s  %[bs0], %[b0], %[c0], %[bs0];"
                       "fnmsub.s  %[bs1], %[b1], %[c1], %[bs1];"
                       "fmadd.s   %[as0], %[b0], %[d0], %[as0];"
                       "fmadd.s   %[as1], %[b1], %[d1], %[as1];"
                       "fnmsub.s  %[bs0], %[a0], %[d0], %[bs0];"
                       "fnmsub.s  %[bs1], %[a1], %[d1], %[bs1];"
                       : [as0] "+&r"(as0), [as1] "+&r"(as1), [bs0] "+&r"(bs0),
                         [bs1] "+&r"(bs1)
                       : [a0] "r"(a0), [a1] "r"(a1), [b0] "r"(b0), [b1] "r"(b1),
                         [c0] "r"(c0), [c1] "r"(c1), [d0] "r"(d0), [d1] "r"(d1)
                       :);
        }
      }
      // Partial sums
      asm volatile("fadd.s %[as0], %[as1], %[as0];"
                   "fadd.s %[bs0], %[bs1], %[bs0];"
                   : [as0] "+&r"(as0), [bs0] "+&r"(bs0)
                   : [as1] "r"(as1), [bs1] "r"(bs1)
                   :);

      /* COMPUTE THE NEW DATA (& DIFFERENCE)*/
      asm volatile(
          // divide the result by the pivot & compute difference
          "fmul.s    %[as0], %[as0], %[den];"
          "fmul.s    %[bs0], %[bs0], %[den];"
          : [as0] "+&r"(as0), [bs0] "+&r"(bs0)
          : [den] "r"(den)
          :);
      // Load the previous result
      a0 = px[2U * i];
      b0 = px[2U * i + 1];
      asm volatile("fsub.s    %[a0], %[a0], %[as0];"
                   "fsub.s    %[b0], %[b0], %[bs0];"
                   : [a0] "+&r"(a0), [b0] "+&r"(b0)
                   : [as0] "r"(as0), [bs0] "r"(bs0)
                   :);
      // Add absolute value to total difference
      a0 = (a0 > 0.0f) ? a0 : (-a0);
      b0 = (b0 > 0.0f) ? b0 : (-b0);
      asm volatile("fadd.s %[diff], %[a0], %[diff];"
                   "fadd.s %[diff], %[b0], %[diff];"
                   : [diff] "+&r"(diff)
                   : [a0] "r"(a0), [b0] "r"(b0)
                   :);

      /* STORE THE RESULT */
      px[2U * i] = as0;
      px[2U * i + 1U] = bs0;
    }

    /* COMPUTE THE ERROR */
    asm volatile(
        // divide the result by the pivot
        "fdiv.s    %[error], %[diff], %[n_samples];"
        : [error] "+&r"(error)
        : [diff] "r"(diff), [n_samples] "r"(2.0f * (float)n)
        :);
    if (error < tol)
      break;
  }
  return;
}
