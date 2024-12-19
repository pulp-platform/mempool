// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

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
void mempool_hermitian_f32p(float *pH, float *pG, float *pS,
                            const uint32_t n_rx, const uint32_t n_tx,
                            const uint32_t folded, const uint32_t zf,
                            const uint32_t core_id, const uint32_t nPE) {

  uint32_t i, j, k;
  float a;
  float b;
  float c0, c1, c2, c3;
  float d0, d1, d2, d3;
  float as0, as1, as2, as3;
  float bs0, bs1, bs2, bs3;
  for (i = core_id; i < n_tx; i += nPE) {
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
        // Compute diagonal element
        if (i == j) {
          asm volatile("fadd.s  %0, %0, %1;" : "+&r"(as0) : "r"(pS[2U * i]));
          bs0 = 0.0f;
        } else if (i == (j + 1U)) {
          asm volatile("fadd.s  %0, %0, %1;" : "+&r"(as1) : "r"(pS[2U * i]));
          bs1 = 0.0f;
        } else if (i == (j + 2U)) {
          asm volatile("fadd.s  %0, %0, %1;" : "+&r"(as2) : "r"(pS[2U * i]));
          bs2 = 0.0f;
        } else if (i == (j + 3U)) {
          asm volatile("fadd.s  %0, %0, %1;" : "+&r"(as3) : "r"(pS[2U * i]));
          bs3 = 0.0f;
        }
      }
      uint32_t const offset = folded ? NUM_BANKS : n_tx;
      // Store
      pG[2 * (i * offset + j)] = as0;
      pG[2 * (i * offset + j + 1U)] = as1;
      pG[2 * (i * offset + j + 2U)] = as2;
      pG[2 * (i * offset + j + 3U)] = as3;
      pG[2 * (i * offset + j) + 1U] = bs0;
      pG[2 * (i * offset + j + 1U) + 1U] = bs1;
      pG[2 * (i * offset + j + 2U) + 1U] = bs2;
      pG[2 * (i * offset + j + 3U) + 1U] = bs3;
    }
  }
  mempool_log_partial_barrier(2, mempool_get_core_id(), nPE);
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
void mempool_MVP_conjtransp_f32p(float *pH, float *pb, float *py,
                                 const uint32_t n_rx, const uint32_t n_tx,
                                 const uint32_t core_id, const uint32_t nPE) {

  uint32_t i, j;
  float a0, a1, a2, a3;
  float b0, b1, b2, b3;
  float c, d;
  float as0, as1, as2, as3;
  float bs0, bs1, bs2, bs3;

  for (i = core_id; i < n_tx; i += 4 * nPE) {
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
  }
  mempool_log_partial_barrier(2, mempool_get_core_id(), nPE);
  return;
}
