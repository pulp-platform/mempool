// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

/**
  @brief         Block-type channel estimation.
  @param[in]     pH  points to output channel
  @param[in]     pPilotRX points to received symbol
  @param[in]     pPilotTX points to sent pilot
  @param[in]     nTX Number of transmitters
  @param[in]     nRX Number of receivers
  @param[in]     nSc Number of Subcarriers
  @return        none
*/
void mempool_chest_q16s_unrolled4(int16_t *pH, int16_t *pPilotRX,
                                  int16_t *pPilotTX, uint32_t nRX, uint32_t nTX,
                                  uint32_t nSc) {

  int32_t re0, re1, re2, re3;
  int32_t im0, im1, im2, im3;

  int16_t a;
  int16_t b;
  int32_t D0, D1, D2, D3;
  int16_t c0, c1, c2, c3;
  int16_t d0, d1, d2, d3;

  // int16_t a0, a1, a2, a3;
  // int16_t b0, b1, b2, b3;
  // int16_t D;
  // int16_t c;
  // int16_t d;

  for (uint32_t k = 0; k < nSc; k++) {
    // for(uint32_t i = 0; i < (nRX >> 2U); i+=4) {
    for (uint32_t i = 0; i < nRX; i++) {

      a = (int16_t)pPilotRX[2U * i];
      b = (int16_t)pPilotRX[2U * i + 1];
      //      a0 = (int16_t)pPilotRX[2U * i];
      //      a1 = (int16_t)pPilotRX[2U * (i + 1)];
      //      a2 = (int16_t)pPilotRX[2U * (i + 2)];
      //      a3 = (int16_t)pPilotRX[2U * (i + 3)];
      //      b0 = (int16_t)pPilotRX[2U * i + 1];
      //      b1 = (int16_t)pPilotRX[2U * (i + 1) + 1];
      //      b2 = (int16_t)pPilotRX[2U * (i + 2) + 1];
      //      b3 = (int16_t)pPilotRX[2U * (i + 3) + 1];

      // for(uint32_t j = 0; j < nTX; j++) {
      for (uint32_t j = 0; j < nTX; j += 4) {

        //        //printf("%d,%d\n", a, b);
        //        uint32_t S = (1 << 8U);
        //        c0 = pPilotTX[2 * j];
        //        c1 = pPilotTX[2 * (j + 1)];
        //        c2 = pPilotTX[2 * (j + 2)];
        //        c3 = pPilotTX[2 * (j + 3)];
        //        d0 = pPilotTX[2 * j + 1];
        //        d1 = pPilotTX[2 * (j + 1) + 1];
        //        d2 = pPilotTX[2 * (j + 2) + 1];
        //        d3 = pPilotTX[2 * (j + 3) + 1];
        //        asm volatile (
        //          "mul     %[D0], %[c0], %[c0];"
        //          "mul     %[D1], %[c1], %[c1];"
        //          "mul     %[D2], %[c2], %[c2];"
        //          "mul     %[D3], %[c3], %[c3];"
        //          "p.mac   %[D0], %[d0], %[d0];"
        //          "p.mac   %[D1], %[d1], %[d1];"
        //          "p.mac   %[D2], %[d2], %[d2];"
        //          "p.mac   %[D3], %[d3], %[d3];"
        //          "mul     %[re0], %[b], %[d0];"
        //          "mul     %[re1], %[b], %[d1];"
        //          "mul     %[re2], %[b], %[d2];"
        //          "mul     %[re3], %[b], %[d3];"
        //          "mul     %[im0], %[b], %[c0];"
        //          "mul     %[im1], %[b], %[c1];"
        //          "mul     %[im2], %[b], %[c2];"
        //          "mul     %[im3], %[b], %[c3];"
        //          "div     %[D0], %[S], %[D0];"
        //          "div     %[D1], %[S], %[D1];"
        //          "div     %[D2], %[S], %[D2];"
        //          "div     %[D3], %[S], %[D3];"
        //          "p.mac   %[re0], %[c0], %[a];"
        //          "p.mac   %[re1], %[c1], %[a];"
        //          "p.mac   %[re2], %[c2], %[a];"
        //          "p.mac   %[re3], %[c3], %[a];"
        //          "p.msu   %[im0], %[d0], %[a];"
        //          "p.msu   %[im1], %[d1], %[a];"
        //          "p.msu   %[im2], %[d2], %[a];"
        //          "p.msu   %[im3], %[d3], %[a];"
        //          "mul     %[re0], %[re0], %[D0];"
        //          "mul     %[re1], %[re1], %[D1];"
        //          "mul     %[re2], %[re2], %[D2];"
        //          "mul     %[re3], %[re3], %[D3];"
        //          "mul     %[im0], %[im0], %[D0];"
        //          "mul     %[im1], %[im1], %[D1];"
        //          "mul     %[im2], %[im2], %[D2];"
        //          "mul     %[im3], %[im3], %[D3];"
        //          "srai    %[re0], %[re0], 0x8;"
        //          "srai    %[re1], %[re1], 0x8;"
        //          "srai    %[re2], %[re2], 0x8;"
        //          "srai    %[re3], %[re3], 0x8;"
        //          "srai    %[im0], %[im0], 0x8;"
        //          "srai    %[im1], %[im1], 0x8;"
        //          "srai    %[im2], %[im2], 0x8;"
        //          "srai    %[im3], %[im3], 0x8;"
        //          : [re0] "=&r"(re0), [re1] "=&r"(re1), [re2] "=&r"(re2),
        //          [re3] "=&r"(re3),
        //            [im0] "=&r"(im0), [im1] "=&r"(im1), [im2] "=&r"(im2),
        //            [im3] "=&r"(im3), [D0] "=&r"(D0), [D1] "=&r"(D1), [D2]
        //            "=&r"(D2), [D3] "=&r"(D3)
        //          : [c0] "r"(c0), [c1] "r"(c1), [c2] "r"(c2), [c3] "r"(c3),
        //            [d0] "r"(d0), [d1] "r"(d1), [d2] "r"(d2), [d3] "r"(d3),
        //            [a] "r" (a), [b] "r" (b), [S] "r" (S)
        //        );
        //        // Store real part
        //        pH[2 * (i * nTX + j    )] = (int16_t) re0;
        //        pH[2 * (i * nTX + j + 1)] = (int16_t) re1;
        //        pH[2 * (i * nTX + j + 2)] = (int16_t) re2;
        //        pH[2 * (i * nTX + j + 3)] = (int16_t) re3;
        //        // Store imaginary part
        //        pH[2 * (i * nTX + j     ) + 1] = (int16_t) im0;
        //        pH[2 * (i * nTX + j + 1 ) + 1] = (int16_t) im1;
        //        pH[2 * (i * nTX + j + 2 ) + 1] = (int16_t) im2;
        //        pH[2 * (i * nTX + j + 3 ) + 1] = (int16_t) im3;

        c0 = (int16_t)pPilotTX[2 * j];
        c1 = (int16_t)pPilotTX[2 * (j + 1)];
        c2 = (int16_t)pPilotTX[2 * (j + 2)];
        c3 = (int16_t)pPilotTX[2 * (j + 3)];
        d0 = (int16_t)pPilotTX[2 * j + 1];
        d1 = (int16_t)pPilotTX[2 * (j + 1) + 1];
        d2 = (int16_t)pPilotTX[2 * (j + 2) + 1];
        d3 = (int16_t)pPilotTX[2 * (j + 3) + 1];
        // Denominator
        D0 = c0 * c0;
        D1 = c1 * c1;
        D2 = c2 * c2;
        D3 = c3 * c3;
        D0 += d0 * d0;
        D1 += d1 * d1;
        D2 += d2 * d2;
        D3 += d3 * d3;
        D0 = (1 << 8U) / D0;
        D1 = (1 << 8U) / D1;
        D2 = (1 << 8U) / D2;
        D3 = (1 << 8U) / D3;
        // Real
        re0 = a * c0;
        re1 = a * c1;
        re2 = a * c2;
        re3 = a * c3;
        re0 += b * d0;
        re1 += b * d1;
        re2 += b * d2;
        re3 += b * d3;
        // Imaginary
        im0 = b * c0;
        im1 = b * c1;
        im2 = b * c2;
        im3 = b * c3;
        im0 -= a * d0;
        im1 -= a * d1;
        im2 -= a * d2;
        im3 -= a * d3;
        re0 = (re0 * D0) >> 8U;
        re1 = (re1 * D1) >> 8U;
        re2 = (re2 * D2) >> 8U;
        re3 = (re3 * D3) >> 8U;
        im0 = (im0 * D0) >> 8U;
        im1 = (im1 * D1) >> 8U;
        im2 = (im2 * D2) >> 8U;
        im3 = (im3 * D3) >> 8U;
        // Store real part
        pH[2 * (i * nTX + j)] = (int16_t)re0;
        pH[2 * (i * nTX + j + 1)] = (int16_t)re1;
        pH[2 * (i * nTX + j + 2)] = (int16_t)re2;
        pH[2 * (i * nTX + j + 3)] = (int16_t)re3;
        // Store imaginary part
        pH[2 * (i * nTX + j) + 1] = (int16_t)im0;
        pH[2 * (i * nTX + j + 1) + 1] = (int16_t)im1;
        pH[2 * (i * nTX + j + 2) + 1] = (int16_t)im2;
        pH[2 * (i * nTX + j + 3) + 1] = (int16_t)im3;
        // dump_x(j);

        //        c = (int32_t)pPilotTX[2*j];
        //        d = (int32_t)pPilotTX[2*j+1];
        //        D = c * c;
        //        // Real
        //        re0  = c * a0;
        //        re1  = c * a1;
        //        re2  = c * a2;
        //        re3  = c * a3;
        //        D += d * d;
        //        re0 += d * b0;
        //        re1 += d * b1;
        //        re2 += d * b2;
        //        re3 += d * b3;
        //        D = (1 << 8) / D;
        //        // Imaginarey
        //        im0  = c * b0;
        //        im1  = c * b1;
        //        im2  = c * b2;
        //        im3  = c * b3;
        //        im0 -= d * a0;
        //        im1 -= d * a1;
        //        im2 -= d * a2;
        //        im3 -= d * a3;
        //        re0 = (re0 * D) >> 8;
        //        re1 = (re1 * D) >> 8;
        //        re2 = (re2 * D) >> 8;
        //        re3 = (re3 * D) >> 8;
        //        im0 = (im0 * D) >> 8;
        //        im1 = (im1 * D) >> 8;
        //        im2 = (im2 * D) >> 8;
        //        im3 = (im3 * D) >> 8;
        //        // Store real part
        //        pH[2*((i + 0) * nTX + j)] = (int16_t) re0;
        //        pH[2*((i + 1) * nTX + j)] = (int16_t) re1;
        //        pH[2*((i + 2) * nTX + j)] = (int16_t) re2;
        //        pH[2*((i + 3) * nTX + j)] = (int16_t) re3;
        //        // Store imaginary part
        //        pH[2*((i + 0) * nTX + j) + 1] = (int16_t) im0;
        //        pH[2*((i + 1) * nTX + j) + 1] = (int16_t) im1;
        //        pH[2*((i + 2) * nTX + j) + 1] = (int16_t) im2;
        //        pH[2*((i + 3) * nTX + j) + 1] = (int16_t) im3;
      }
    }
    pPilotTX += 2 * nTX;
    pPilotRX += 2 * nRX;
    pH += 2 * (nTX * nRX);
  }
  return;
}

/**
  @brief         Block-type channel estimation.
  @param[in]     pH  points to output channel
  @param[in]     pPilotRX points to received symbol
  @param[in]     pPilotTX points to sent pilot
  @param[in]     nTX Number of transmitters
  @param[in]     nRX Number of receivers
  @param[in]     nSc Number of Subcarriers
  @return        none
*/
void mempool_chest_q16s_unrolled2(int16_t *pH, int16_t *pPilotRX,
                                  int16_t *pPilotTX, uint32_t nRX, uint32_t nTX,
                                  uint32_t nSc) {

  int32_t re0, re1;
  int32_t i0, i1;

  int32_t a;
  int32_t b;
  int32_t D0, D1;
  int32_t c0, c1;
  int32_t d0, d1;

  for (uint32_t k = 0; k < nSc; k++) {
    for (uint32_t i = 0; i < nRX; i++) {

      a = (int32_t)pPilotRX[2 * i];
      b = (int32_t)pPilotRX[2 * i + 1];
      for (uint32_t j = 0; j < (nTX >> 1U); j += 2) {

        c0 = (int32_t)pPilotTX[2 * j];
        c1 = (int32_t)pPilotTX[2 * (j + 1)];
        d0 = (int32_t)pPilotTX[2 * j + 1];
        d1 = (int32_t)pPilotTX[2 * (j + 1) + 1];
        // Denominator
        D0 = c0 * c0;
        D1 = c1 * c1;
        D0 += d0 * d0;
        D1 += d1 * d1;
        D0 = (1 << 8U) / D0;
        D1 = (1 << 8U) / D1;
        // Real
        re0 = a * c0;
        re1 = a * c1;
        re0 += b * d0;
        re1 += b * d1;
        // Imaginarey
        i0 = b * c0;
        i1 = b * c1;
        i0 -= a * d0;
        i1 -= a * d1;
        re0 = (re0 * D0) >> 8U;
        re1 = (re1 * D1) >> 8U;
        i0 = (i0 * D0) >> 8U;
        i1 = (i1 * D1) >> 8U;
        // Store real part
        pH[2 * (i * nTX + j)] = (int16_t)re0;
        pH[2 * (i * nTX + j + 1)] = (int16_t)re1;
        // Store imaginary part
        pH[2 * (i * nTX + j) + 1] = (int16_t)i0;
        pH[2 * (i * nTX + j + 1) + 1] = (int16_t)i1;
      }
    }
    pPilotTX += 2 * nTX;
    pPilotRX += 2 * nRX;
    pH += 2 * (nTX * nRX);
  }
  return;
}

/* a[i] = ar[i] + i * ai[j]

   out[i][j] = a[i] / c[j]
   out[i][j + 1] = a[i] / c[j + 1]
   out[i][j + 2] = a[i] / c[j + 2]
   out[i][j + 3] = a[i] / c[j + 3]*/

static inline void inner_loop(int16_t *pPilotTX, int16_t *pH, uint32_t nTX,
                              v2s ab, v2s ab_n, uint32_t i, uint32_t j) {

  v2s cd0, cd1, cd2, cd3;
  int32_t re0, re1, re2, re3;
  int32_t im0, im1, im2, im3;
  int32_t D0, D1, D2, D3;
  int32_t S = (1 << 8U);
  //    cd = *(v2s *)&pPilotTX[2U * j];
  //    D = (int32_t)__DOTP2(cd, cd);
  //    D = (1 << 8) / D;
  //    re = (int32_t)__DOTP2(ab, cd);
  //    t0 = ab[0];
  //    t1 = ab[1];
  //    ab_t = __PACK2(t0, -t1);
  //    im = (int32_t)__DOTP2(ab_t, cd);
  //    re = (re * D) >> 8U;
  //    im = (im * D) >> 8U;
  cd0 = *(v2s *)&pPilotTX[2U * j];
  cd1 = *(v2s *)&pPilotTX[2U * (j + 1)];
  cd2 = *(v2s *)&pPilotTX[2U * (j + 2)];
  cd3 = *(v2s *)&pPilotTX[2U * (j + 3)];
  asm volatile(
      // Compute denominator
      "pv.dotsp.h    %[D0],  %[cd0],  %[cd0];"
      "pv.dotsp.h    %[D1],  %[cd1],  %[cd1];"
      "pv.dotsp.h    %[D2],  %[cd2],  %[cd2];"
      "pv.dotsp.h    %[D3],  %[cd3],  %[cd3];"
      "div           %[D0],  %[S],    %[D0];"
      "div           %[D1],  %[S],    %[D1];"
      "div           %[D2],  %[S],    %[D2];"
      "div           %[D3],  %[S],    %[D3];"
      // Compute numerator
      "pv.dotsp.h    %[re0], %[ab],   %[cd0];"
      "pv.dotsp.h    %[re1], %[ab],   %[cd1];"
      "pv.dotsp.h    %[re2], %[ab],   %[cd2];"
      "pv.dotsp.h    %[re3], %[ab],   %[cd3];"
      "pv.dotsp.h    %[im0], %[ab_n], %[cd0];"
      "pv.dotsp.h    %[im1], %[ab_n], %[cd1];"
      "pv.dotsp.h    %[im2], %[ab_n], %[cd2];"
      "pv.dotsp.h    %[im3], %[ab_n], %[cd3];"
      "mul           %[re0], %[re0],  %[D0];"
      "mul           %[re1], %[re1],  %[D1];"
      "mul           %[re2], %[re2],  %[D2];"
      "mul           %[re3], %[re3],  %[D3];"
      "mul           %[im0], %[im0],  %[D0];"
      "mul           %[im1], %[im1],  %[D1];"
      "mul           %[im2], %[im2],  %[D2];"
      "mul           %[im3], %[im3],  %[D3];"
      // Rescale after division
      "srai          %[re0], %[re0],  0x8;"
      "srai          %[im0], %[im0],  0x8;"
      "srai          %[re1], %[re1],  0x8;"
      "srai          %[im1], %[im1],  0x8;"
      "srai          %[re2], %[re2],  0x8;"
      "srai          %[im2], %[im2],  0x8;"
      "srai          %[re3], %[re3],  0x8;"
      "srai          %[im3], %[im3],  0x8;"
      // Clip to 16b
      "p.clip        %[re0], %[re0],  0x16;"
      "p.clip        %[im0], %[im0],  0x16;"
      "p.clip        %[re1], %[re1],  0x16;"
      "p.clip        %[im1], %[im1],  0x16;"
      "p.clip        %[re1], %[re1],  0x16;"
      "p.clip        %[im1], %[im1],  0x16;"
      "p.clip        %[re2], %[re2],  0x16;"
      "p.clip        %[im2], %[im2],  0x16;"
      "p.clip        %[re3], %[re3],  0x16;"
      "p.clip        %[im3], %[im3],  0x16;"
      // Pack in 32b word
      "pv.pack       %[re0], %[re0], %[im0];"
      "pv.pack       %[re1], %[re1], %[im1];"
      "pv.pack       %[re2], %[re2], %[im2];"
      "pv.pack       %[re3], %[re3], %[im3];"
      : [D0] "=&r"(D0), [D1] "=&r"(D1), [D2] "=&r"(D2), [D3] "=&r"(D3),
        [re0] "=&r"(re0), [re1] "=&r"(re1), [re2] "=&r"(re2), [re3] "=&r"(re3),
        [im0] "=&r"(im0), [im1] "=&r"(im1), [im2] "=&r"(im2), [im3] "=&r"(im3)
      : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2), [cd3] "r"(cd3),
        [ab] "r"(ab), [ab_n] "r"(ab_n), [S] "r"(S)
      :);
  *((v2s *)&pH[2 * (i * nTX + j)]) = (v2s)re0;
  *((v2s *)&pH[2 * (i * nTX + j + 1)]) = (v2s)re1;
  *((v2s *)&pH[2 * (i * nTX + j + 2)]) = (v2s)re2;
  *((v2s *)&pH[2 * (i * nTX + j + 3)]) = (v2s)re3;
  return;
}

/**
  @brief         Block-type channel estimation.
  @param[in]     pH  points to output channel
  @param[in]     pPilotRX points to received symbol
  @param[in]     pPilotTX points to sent pilot
  @param[in]     nTX Number of transmitters
  @param[in]     nRX Number of receivers
  @param[in]     nSc Number of Subcarriers
  @return        none
*/
void mempool_chest_q16s_unrolled4_xpulpv2(int16_t *pH, int16_t *pPilotRX,
                                          int16_t *pPilotTX, uint32_t nRX,
                                          uint32_t nTX, uint32_t nSc) {

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;

  for (uint32_t k = 0; k < nSc; k++) {
    for (uint32_t i = 0; i < nRX; i += 4) {

      ab0 = *(v2s *)&pPilotRX[2U * i];
      ab1 = *(v2s *)&pPilotRX[2U * (i + 1)];
      ab2 = *(v2s *)&pPilotRX[2U * (i + 2)];
      ab3 = *(v2s *)&pPilotRX[2U * (i + 3)];
      asm volatile(
          "pv.sub.h      %[ab_n0], %[zero], %[ab0];"
          "pv.sub.h      %[ab_n1], %[zero], %[ab1];"
          "pv.sub.h      %[ab_n2], %[zero], %[ab2];"
          "pv.sub.h      %[ab_n3], %[zero], %[ab3];"
          "pv.shuffle2.h %[ab_n0], %[ab0],  %[mask];"
          "pv.shuffle2.h %[ab_n1], %[ab1],  %[mask];"
          "pv.shuffle2.h %[ab_n2], %[ab2],  %[mask];"
          "pv.shuffle2.h %[ab_n3], %[ab3],  %[mask];"
          : [ab_n0] "=&r"(ab_n0), [ab_n1] "=&r"(ab_n1), [ab_n2] "=&r"(ab_n2),
            [ab_n3] "=&r"(ab_n3)
          : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),
            [zero] "r"((v2s){0, 0}), [mask] "r"((v2s){0x1, 0x2})
          :);
      for (uint32_t j = 0; j < nTX; j += 4) {
        inner_loop(pPilotTX, pH, nTX, ab0, ab_n0, i, j);
        inner_loop(pPilotTX, pH, nTX, ab1, ab_n1, i + 1, j);
        inner_loop(pPilotTX, pH, nTX, ab2, ab_n2, i + 2, j);
        inner_loop(pPilotTX, pH, nTX, ab3, ab_n3, i + 3, j);
      }
    }
    pPilotTX += 2 * nTX;
    pPilotRX += 2 * nRX;
    pH += 2 * (nTX * nRX);
  }
  return;
}
