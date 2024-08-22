// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

void mempool_hermitian_f16s(__fp16 *pH, __fp16 *pG, __fp16 *sigma,
                            const uint32_t n_rx, const uint32_t n_tx,
                            const uint32_t folded, const uint32_t zf);
void mempool_MVP_conjtransp_f16s(__fp16 *pH, __fp16 *pb, __fp16 *py,
                                 const uint32_t n_rx, const uint32_t n_tx,
                                 const uint32_t folded);

/* Computes the Hermitian matrix G = (H'*H + sigma^2I) */
void mempool_hermitian_f16s(__fp16 *pH, __fp16 *pG, __fp16 *sigma,
                            const uint32_t n_rx, const uint32_t n_tx,
                            const uint32_t folded, const uint32_t zf) {

  uint32_t i, j, k;
  __fp16 a;
  __fp16 b;
  __fp16 c0, c1, c2, c3;
  __fp16 d0, d1, d2, d3;
  __fp16 as0, as1, as2, as3;
  __fp16 bs0, bs1, bs2, bs3;
  for (i = 0; i < n_tx; i++) {
    for (j = 0; j < n_tx; j += 4) {
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
        asm volatile(
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
          asm volatile("fadd.h  %[as0], %[as0], %[sigma];"
                       : [as0] "+&r"(as0)
                       : [sigma] "r"(sigma[2 * i])
                       :);
          bs0 = (__fp16)0.0f;
        } else if (i == (j + 1U)) {
          asm volatile("fadd.h  %[as1], %[as1], %[sigma];"
                       : [as1] "+&r"(as1)
                       : [sigma] "r"(sigma[2 * i])
                       :);
          bs1 = (__fp16)0.0f;
        } else if (i == (j + 2U)) {
          asm volatile("fadd.h  %[as2], %[as2], %[sigma];"
                       : [as2] "+&r"(as2)
                       : [sigma] "r"(sigma[2 * i])
                       :);
          bs2 = (__fp16)0.0f;
        } else if (i == (j + 3U)) {
          asm volatile("fadd.h  %[as3], %[as3], %[sigma];"
                       : [as3] "+&r"(as3)
                       : [sigma] "r"(sigma[2 * i])
                       :);
          bs3 = (__fp16)0.0f;
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
        // uint32_t addr = i * (n_tx / 4) * N_BANKS + (j / 4) * N_BANKS;
        uint32_t addr = i * N_BANKS;
        // Store
        pG[addr] = as0;
        pG[addr + 1U] = bs0;
        pG[addr + 2U] = as1;
        pG[addr + 3U] = bs1;
        pG[addr + 4U] = as2;
        pG[addr + 5U] = bs2;
        pG[addr + 6U] = as3;
        pG[addr + 7U] = bs3;
      }
    }
  }
  return;
}

/* Computes the Hermitian matrix G = (H'*H + sigma^2I) */
void mempool_hermitian_f16vecs(__fp16 *pH, __fp16 *pG, __fp16 *sigma,
                               const uint32_t n_rx, const uint32_t n_tx) {

  uint32_t i, j, k;
  v2h ab;
  v2h cd0, cd1, cd2, cd3;
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
        ab = (*(v2h *)&pH[2U * (k * n_tx + i)]);
        // inputs from matrix H
        cd0 = (*(v2h *)&pH[2U * (k * n_tx + j)]);
        cd1 = (*(v2h *)&pH[2U * (k * n_tx + j + 1U)]);
        cd2 = (*(v2h *)&pH[2U * (k * n_tx + j + 2U)]);
        cd3 = (*(v2h *)&pH[2U * (k * n_tx + j + 3U)]);

        uint32_t ndc0, ndc1, ndc2, ndc3;
        const uint32_t val = 0x3C00BC00;
        const uint32_t mask = 0x00010002;

        // dotproducts (ac + bd) + j (ad - bc)
        asm volatile(
            // a * c + b * d
            "vfdotpex.s.h  %[as0], %[ab], %[cd0];"
            "vfdotpex.s.h  %[as1], %[ab], %[cd1];"
            "vfdotpex.s.h  %[as2], %[ab], %[cd2];"
            "vfdotpex.s.h  %[as3], %[ab], %[cd3];"
            //
            "pv.shuffle2.h  %[ndc0], %[cd0], %[mask];"
            "pv.shuffle2.h  %[ndc1], %[cd1], %[mask];"
            "pv.shuffle2.h  %[ndc2], %[cd2], %[mask];"
            "pv.shuffle2.h  %[ndc3], %[cd3], %[mask];"
            //
            "vfmul.h %[ndc0], %[val], %[ndc0];"
            "vfmul.h %[ndc1], %[val], %[ndc1];"
            "vfmul.h %[ndc2], %[val], %[ndc2];"
            "vfmul.h %[ndc3], %[val], %[ndc3];"
            // a * d - b * c
            "vfdotpex.s.h  %[as0], %[ab], %[ndc0];"
            "vfdotpex.s.h  %[as1], %[ab], %[ndc1];"
            "vfdotpex.s.h  %[as2], %[ab], %[ndc2];"
            "vfdotpex.s.h  %[as3], %[ab], %[ndc3];"
            : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
              [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
              [bs2] "+&r"(bs2), [bs3] "+&r"(bs3), [ndc0] "+r"(ndc0),
              [ndc1] "+r"(ndc1), [ndc2] "+r"(ndc2), [ndc3] "+r"(ndc3)
            : [ab] "r"(ab), [val] "r"(val), [mask] "r"(mask), [cd0] "r"(cd0),
              [cd1] "r"(cd1), [cd2] "r"(cd2), [cd3] "r"(cd3)
            :);
      }
      // Compute diagonal elements
      if (i == j) {
        asm volatile("fadd.s  %[as0], %[as0], %[sigma];"
                     : [as0] "+&r"(as0)
                     : [sigma] "r"(sigma[2 * i])
                     :);
        bs0 = 0.0f;
      } else if (i == (j + 1U)) {
        asm volatile("fadd.s  %[as1], %[as1], %[sigma];"
                     : [as1] "+&r"(as1)
                     : [sigma] "r"(sigma[2 * i])
                     :);
        bs1 = 0.0f;
      } else if (i == (j + 2U)) {
        asm volatile("fadd.s  %[as2], %[as2], %[sigma];"
                     : [as2] "+&r"(as2)
                     : [sigma] "r"(sigma[2 * i])
                     :);
        bs2 = 0.0f;
      } else if (i == (j + 3U)) {
        asm volatile("fadd.s  %[as3], %[as3], %[sigma];"
                     : [as3] "+&r"(as3)
                     : [sigma] "r"(sigma[2 * i])
                     :);
        bs3 = 0.0f;
      }
      // Store
      v2h res0, res1, res2, res3;
      asm volatile(
          "vfcpka.h.s %[res0], %[as0], %[bs0];"
          "vfcpka.h.s %[res1], %[as1], %[bs1];"
          "vfcpka.h.s %[res2], %[as2], %[bs2];"
          "vfcpka.h.s %[res3], %[as3], %[bs3];"
          : [res0] "=&r"(res0), [res1] "=&r"(res1), [res2] "=&r"(res2),
            [res3] "=&r"(res3)
          : [as0] "r"(as0), [as1] "r"(as1), [as2] "r"(as2), [as3] "r"(as3),
            [bs0] "r"(bs0), [bs1] "r"(bs1), [bs2] "r"(bs2), [bs3] "r"(bs3)
          :);
      (*(v2h *)&pG[2 * (i * n_tx + j)]) = res0;
      (*(v2h *)&pG[2 * (i * n_tx + j + 1U)]) = res1;
      (*(v2h *)&pG[2 * (i * n_tx + j + 2U)]) = res2;
      (*(v2h *)&pG[2 * (i * n_tx + j + 3U)]) = res3;
      j += 4;
    } while (j < (n_tx >> 2U));
  }
  return;
}

void mempool_MVP_conjtransp_f16s(__fp16 *pH, __fp16 *pb, __fp16 *py,
                                 const uint32_t n_rx, const uint32_t n_tx,
                                 const uint32_t folded) {

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
      asm volatile(
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
      uint32_t addr = (i / 4) * N_BANKS;
      py[addr] = as0;
      py[addr + 1U] = bs0;
      py[addr + 2U] = as1;
      py[addr + 3U] = bs1;
      py[addr + 4U] = as2;
      py[addr + 5U] = bs2;
      py[addr + 6U] = as3;
      py[addr + 7U] = bs3;
      i += 4;
    }

  } while (i < n_tx);
  return;
}
