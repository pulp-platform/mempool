// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich
// Author: Aofeng Aoshen, ETH Zurich

#pragma once
#include "builtins_v2.h"

/**
  @brief         Computes the Hermitian matrix G = (H'*H + pS^2I).
  @param[in]     pH     points to input matrix
  @param[in]     pG     points to output matrix
  @param[in]     pS     points to the noise vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @param[in]     zf     controls if the zero forcing is used
  @return        none
*/
void mempool_hermitian_f8s(__fp8 *pH, __fp8 *pS, __fp16 *pG,
                           const uint32_t n_rx, const uint32_t n_tx,
                           const uint32_t zf, const uint32_t folded) {

  uint32_t i, j, k;
  __fp8 a;
  __fp8 b;

  __fp8 c0, c1, c2, c3;
  __fp8 d0, d1, d2, d3;
  __fp8 as0, as1, as2, as3;
  __fp8 bs0, bs1, bs2, bs3;
  for (i = 0; i < n_tx; i++) {
    for (j = 0; j < n_tx; j += 4) {
      // Initialize the real part of sums
      as0 = (__fp8)0U;
      as1 = (__fp8)0U;
      as2 = (__fp8)0U;
      as3 = (__fp8)0U;
      // Initialize the imag part of sums
      bs0 = (__fp8)0U;
      bs1 = (__fp8)0U;
      bs2 = (__fp8)0U;
      bs3 = (__fp8)0U;
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
            "fmadd.b  %[as0], %[a], %[c0], %[as0];"
            "fmadd.b  %[as1], %[a], %[c1], %[as1];"
            "fmadd.b  %[as2], %[a], %[c2], %[as2];"
            "fmadd.b  %[as3], %[a], %[c3], %[as3];"
            // a * d
            "fmadd.b  %[bs0], %[a], %[d0], %[bs0];"
            "fmadd.b  %[bs1], %[a], %[d3], %[bs1];"
            "fmadd.b  %[bs2], %[a], %[d2], %[bs2];"
            "fmadd.b  %[bs3], %[a], %[d3], %[bs3];"
            // b * d
            "fmadd.b  %[as0], %[b], %[d0], %[as0];"
            "fmadd.b  %[as1], %[b], %[d1], %[as1];"
            "fmadd.b  %[as2], %[b], %[d2], %[as2];"
            "fmadd.b  %[as3], %[b], %[d3], %[as3];"
            // - b * c
            "fnmsub.b %[bs0], %[b], %[c0], %[bs0];"
            "fnmsub.b %[bs1], %[b], %[c1], %[bs1];"
            "fnmsub.b %[bs2], %[b], %[c2], %[bs2];"
            "fnmsub.b %[bs3], %[b], %[c3], %[bs3];"
            : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
              [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
              [bs2] "+&r"(bs2), [bs3] "+&r"(bs3)
            : [a] "r"(a), [b] "r"(b), [c0] "r"(c0), [c1] "r"(c1), [c2] "r"(c2),
              [c3] "r"(c3), [d0] "r"(d0), [d1] "r"(d1), [d2] "r"(d2),
              [d3] "r"(d3)
            :);
      }
      __fp16 FP16_as0, FP16_as1, FP16_as2, FP16_as3;
      __fp16 FP16_bs0, FP16_bs1, FP16_bs2, FP16_bs3;
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as0) : "r"(as0) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as1) : "r"(as1) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as2) : "r"(as2) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as3) : "r"(as3) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs0) : "r"(bs0) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs1) : "r"(bs1) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs2) : "r"(bs2) :);
      asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs3) : "r"(bs3) :);

      if ((zf == 0) && ((i - j) < 4)) {
        __fp8 FP8_s = pS[2 * i];
        __fp16 FP16_s;
        asm volatile("fcvt.h.b %0, %1;" : "=&r"(FP16_s) : "r"(FP8_s));
        // Compute diagonal elements
        if (i == j) {
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(FP16_as0) : "r"(FP16_s));
          FP16_bs0 = (__fp16)0U;
        } else if (i == (j + 1U)) {
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(FP16_as1) : "r"(FP16_s));
          FP16_bs1 = (__fp16)0U;
        } else if (i == (j + 2U)) {
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(FP16_as2) : "r"(FP16_s));
          FP16_bs2 = (__fp16)0U;
        } else if (i == (j + 3U)) {
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(FP16_as3) : "r"(FP16_s));
          FP16_bs3 = (__fp16)0U;
        }
      }
      uint32_t const offset = folded ? N_BANKS : n_tx;
      // Store
      pG[2 * (i * offset + j)] = FP16_as0;
      pG[2 * (i * offset + j + 1U)] = FP16_as1;
      pG[2 * (i * offset + j + 2U)] = FP16_as2;
      pG[2 * (i * offset + j + 3U)] = FP16_as3;
      pG[2 * (i * offset + j) + 1U] = FP16_bs0;
      pG[2 * (i * offset + j + 1U) + 1U] = FP16_bs1;
      pG[2 * (i * offset + j + 2U) + 1U] = FP16_bs2;
      pG[2 * (i * offset + j + 3U) + 1U] = FP16_bs3;
    }
  }
  return;
}

/**
  @brief         Computes the matrix-vector product y = H' * x.
  @param[in]     pH     points to input matrix
  @param[in]     px     points to input vector
  @param[in]     py     points to output vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @return        none
*/
void mempool_MVP_conjtransp_f8s(__fp8 *pH, __fp8 *px, __fp16 *py,
                                const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j;
  __fp8 a0, a1, a2, a3;
  __fp8 b0, b1, b2, b3;
  __fp8 c, d;
  __fp8 as0, as1, as2, as3;
  __fp8 bs0, bs1, bs2, bs3;
  i = 0;
  do {
    // Initialize the real part of sums
    as0 = (__fp8)0.0f;
    as1 = (__fp8)0.0f;
    as2 = (__fp8)0.0f;
    as3 = (__fp8)0.0f;
    // Initialize the imag part of sums
    bs0 = (__fp8)0.0f;
    bs1 = (__fp8)0.0f;
    bs2 = (__fp8)0.0f;
    bs3 = (__fp8)0.0f;
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
      // inputs from vector
      c = px[2U * j];
      d = px[2U * j + 1U];
      asm volatile(
          // a * c
          "fmadd.b  %[as0], %[a0], %[c], %[as0];"
          "fmadd.b  %[as1], %[a1], %[c], %[as1];"
          "fmadd.b  %[as2], %[a2], %[c], %[as2];"
          "fmadd.b  %[as3], %[a3], %[c], %[as3];"
          // a * d
          "fmadd.b  %[bs0], %[a0], %[d], %[bs0];"
          "fmadd.b  %[bs1], %[a1], %[d], %[bs1];"
          "fmadd.b  %[bs2], %[a2], %[d], %[bs2];"
          "fmadd.b  %[bs3], %[a3], %[d], %[bs3];"
          // b * d
          "fmadd.b  %[as0], %[b0], %[d], %[as0];"
          "fmadd.b  %[as1], %[b1], %[d], %[as1];"
          "fmadd.b  %[as2], %[b2], %[d], %[as2];"
          "fmadd.b  %[as3], %[b3], %[d], %[as3];"
          // - b * c
          "fnmsub.b %[bs0], %[b0], %[c], %[bs0];"
          "fnmsub.b %[bs1], %[b1], %[c], %[bs1];"
          "fnmsub.b %[bs2], %[b2], %[c], %[bs2];"
          "fnmsub.b %[bs3], %[b3], %[c], %[bs3];"
          : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
            [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
            [bs2] "+&r"(bs2), [bs3] "+&r"(bs3)
          : [c] "r"(c), [d] "r"(d), [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2),
            [a3] "r"(a3), [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3)
          :);
    }
    // Store
    __fp16 FP16_as0, FP16_as1, FP16_as2, FP16_as3;
    __fp16 FP16_bs0, FP16_bs1, FP16_bs2, FP16_bs3;
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as0) : "r"(as0) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as1) : "r"(as1) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as2) : "r"(as2) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_as3) : "r"(as3) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs0) : "r"(bs0) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs1) : "r"(bs1) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs2) : "r"(bs2) :);
    asm volatile("fcvt.h.b %0, %1;" : "+&r"(FP16_bs3) : "r"(bs3) :);
    py[2U * i] = FP16_as0;
    py[2U * (i + 1U)] = FP16_as1;
    py[2U * (i + 2U)] = FP16_as2;
    py[2U * (i + 3U)] = FP16_as3;
    py[2U * i + 1U] = FP16_bs0;
    py[2U * (i + 1U) + 1U] = FP16_bs1;
    py[2U * (i + 2U) + 1U] = FP16_bs2;
    py[2U * (i + 3U) + 1U] = FP16_bs3;
    i += 4;
  } while (i < n_tx);
  return;
}

void mempool_hermitian_f8vecs(__fp8 *pH, __fp8 *pS, __fp16 *pG,
                              const uint32_t n_rx, const uint32_t n_tx,
                              const uint32_t zf, const uint32_t folded) {

  uint32_t i, j, k;
  uint32_t fe0, fe1, fe2, fe3;
  uint32_t ambba;
  uint32_t dcdc0, dcdc1, dcdc2, dcdc3;

  for (i = 0; i < n_tx; i++) {
    for (j = 0; j < n_tx; j += 4) {

      // Initialize sums
      fe0 = 0U;
      fe1 = 0U;
      fe2 = 0U;
      fe3 = 0U;

      // Inner Loop
      for (k = 0; k < n_rx; k++) {
        // inputs from matrix H_h
        int16_t ba = *(int16_t *)&pH[2U * (k * n_tx + i)];
        // inputs from matrix H
        int16_t dc0 = *(int16_t *)&pH[2U * (k * n_tx + j)];
        int16_t dc1 = *(int16_t *)&pH[2U * (k * n_tx + j + 1U)];
        int16_t dc2 = *(int16_t *)&pH[2U * (k * n_tx + j + 2U)];
        int16_t dc3 = *(int16_t *)&pH[2U * (k * n_tx + j + 3U)];
        // shuffle
        asm volatile(
            "pv.shuffle2.b %[ambba], %[ba], %[mask];"
            "pv.pack  %[dcdc0], %[dc0], %[dc0];"
            "pv.pack  %[dcdc1], %[dc1], %[dc1];"
            "pv.pack  %[dcdc2], %[dc2], %[dc2];"
            "pv.pack  %[dcdc3], %[dc3], %[dc3];"
            // negate operand
            "vfmul.b  %[ambba], %[ambba], %[nmask];"
            : [dcdc0] "=&r"(dcdc0), [dcdc1] "=&r"(dcdc1), [dcdc2] "=&r"(dcdc2),
              [dcdc3] "=&r"(dcdc3), [ambba] "+&r"(ambba), [ba] "+&r"(ba)
            : [dc0] "r"(dc0), [dc1] "r"(dc1), [dc2] "r"(dc2), [dc3] "r"(dc3),
              [mask] "r"(0x04050504), [nmask] "r"(0x3cbc3c3c)
            :);
        // dotproducts e = (ac + bd)  f = j (ad - bc)
        asm volatile(
            "vfdotpex.h.b  %[fe0], %[dcdc0], %[ambba];"
            "vfdotpex.h.b  %[fe1], %[dcdc1], %[ambba];"
            "vfdotpex.h.b  %[fe2], %[dcdc2], %[ambba];"
            "vfdotpex.h.b  %[fe3], %[dcdc3], %[ambba];"
            : [fe0] "+&r"(fe0), [fe1] "+&r"(fe1), [fe2] "+&r"(fe2),
              [fe3] "+&r"(fe3)
            : [dcdc0] "r"(dcdc0), [dcdc1] "r"(dcdc1), [dcdc2] "r"(dcdc2),
              [dcdc3] "r"(dcdc3), [ambba] "r"(ambba));
      }

      if ((zf == 0) && ((i - j) < 4)) {
        __fp8 FP8_sigma = pS[2 * i];
        __fp16 FP16_sigma;
        asm volatile("fcvt.h.b %0, %1;" : "=&r"(FP16_sigma) : "r"(FP8_sigma));
        // Compute diagonal elements
        if (i == j) {
          // printf("%08x\n", *(uint32_t*)&fe0);
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(fe0) : "r"(FP16_sigma));
          asm volatile("and     %0, %0, %1;" : "+&r"(fe0) : "r"(0x0000FFFF));
        } else if (i == (j + 1U)) {
          // printf("%08x\n", *(uint32_t*)&fe1);
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(fe1) : "r"(FP16_sigma));
          asm volatile("and     %0, %0, %1;" : "+&r"(fe1) : "r"(0x0000FFFF));
        } else if (i == (j + 2U)) {
          // printf("%08x\n", *(uint32_t*)&fe2);
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(fe2) : "r"(FP16_sigma));
          asm volatile("and     %0, %0, %1;" : "+&r"(fe2) : "r"(0x0000FFFF));
        } else if (i == (j + 3U)) {
          // printf("%08x\n", *(uint32_t*)&fe3);
          asm volatile("fadd.h  %0, %0, %1;" : "+&r"(fe3) : "r"(FP16_sigma));
          asm volatile("and     %0, %0, %1;" : "+&r"(fe3) : "r"(0x0000FFFF));
        }
      }
      uint32_t const offset = folded ? N_BANKS : n_tx;
      // Store
      (*(uint32_t *)&pG[2 * (i * offset + j)]) = fe0;
      (*(uint32_t *)&pG[2 * (i * offset + j + 1U)]) = fe1;
      (*(uint32_t *)&pG[2 * (i * offset + j + 2U)]) = fe2;
      (*(uint32_t *)&pG[2 * (i * offset + j + 3U)]) = fe3;
    }
  }
  return;
}

void mempool_MVP_conjtransp_f8vecs(__fp8 *pH, __fp8 *px, __fp16 *py,
                                   const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j;
  uint32_t fe0, fe1, fe2, fe3;
  uint32_t ambba0, ambba1, ambba2, ambba3;
  uint32_t dmcdc;

  for (i = 0; i < n_tx; i += 4) {
    // Initialize sums
    fe0 = 0U;
    fe1 = 0U;
    fe2 = 0U;
    fe3 = 0U;
    for (j = 0; j < n_rx; j++) {
      // inputs from matrix H_h
      int16_t ba0 = *(int16_t *)&pH[2U * (j * n_tx + i)];
      int16_t ba1 = *(int16_t *)&pH[2U * (j * n_tx + i + 1U)];
      int16_t ba2 = *(int16_t *)&pH[2U * (j * n_tx + i + 2U)];
      int16_t ba3 = *(int16_t *)&pH[2U * (j * n_tx + i + 3U)];
      // inputs from vector
      int16_t dc = *(int16_t *)&px[2U * j];
      // shuffle
      asm volatile(
          "pv.pack %[dmcdc], %[dc], %[dc];"
          "pv.shuffle2.b %[ambba0], %[ba0], %[mask];"
          "pv.shuffle2.b %[ambba1], %[ba1], %[mask];"
          "pv.shuffle2.b %[ambba2], %[ba2], %[mask];"
          "pv.shuffle2.b %[ambba3], %[ba3], %[mask];"
          // negate operand
          "vfmul.b  %[dmcdc], %[dmcdc], %[nmask];"
          : [ambba0] "=&r"(ambba0), [ambba1] "=&r"(ambba1),
            [ambba2] "=&r"(ambba2), [ambba3] "=&r"(ambba3),
            [dmcdc] "+&r"(dmcdc), [dc] "+&r"(dc)
          : [ba0] "r"(ba0), [ba1] "r"(ba1), [ba2] "r"(ba2), [ba3] "r"(ba3),
            [mask] "r"(0x04050504), [nmask] "r"(0x3cbc3c3c)
          :);
      // printf("2: %08x\n", *(uint32_t*)&dmcdc);
      // dotproducts e = (ac + bd)  f = j (ad - bc)
      asm volatile(
          "vfdotpex.h.b  %[fe0], %[ambba0], %[dmcdc];"
          "vfdotpex.h.b  %[fe1], %[ambba1], %[dmcdc];"
          "vfdotpex.h.b  %[fe2], %[ambba2], %[dmcdc];"
          "vfdotpex.h.b  %[fe3], %[ambba3], %[dmcdc];"
          :
          [fe0] "+&r"(fe0), [fe1] "+&r"(fe1), [fe2] "+&r"(fe2), [fe3] "+&r"(fe3)
          : [ambba0] "r"(ambba0), [ambba1] "r"(ambba1), [ambba2] "r"(ambba2),
            [ambba3] "r"(ambba3), [dmcdc] "r"(dmcdc));
    }

    // Store
    (*(uint32_t *)&py[2U * i]) = fe0;
    (*(uint32_t *)&py[2U * (i + 1U)]) = fe1;
    (*(uint32_t *)&py[2U * (i + 2U)]) = fe2;
    (*(uint32_t *)&py[2U * (i + 3U)]) = fe3;
  }
  return;
}
