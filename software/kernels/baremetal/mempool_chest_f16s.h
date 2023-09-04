// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

/* a[i] = ar[i] + i * ai[j]

   out[i][j] = a[i] / c[j]
   out[i][j + 1] = a[i] / c[j + 1h
   out[i][j + 2] = a[i] / c[j + 2]
   out[i][j + 3] = a[i] / c[j + 3]*/

static inline void chest_unrolled4_inner_loop_f16(__fp16 *pPilotTX, __fp16 *pH,
                                                  uint32_t nTX, uint32_t ab,
                                                  uint32_t ab_n, uint32_t i,
                                                  uint32_t j) {

  uint32_t cd0, cd1, cd2, cd3;
  float re0 = 0.0f, re1 = 0.0f, re2 = 0.0f, re3 = 0.0f;
  float im0 = 0.0f, im1 = 0.0f, im2 = 0.0f, im3 = 0.0f;
  float D0 = 0.0f, D1 = 0.0f, D2 = 0.0f, D3 = 0.0f;
  cd0 = *(uint32_t *)&pPilotTX[2U * j];
  cd1 = *(uint32_t *)&pPilotTX[2U * (j + 1)];
  cd2 = *(uint32_t *)&pPilotTX[2U * (j + 2)];
  cd3 = *(uint32_t *)&pPilotTX[2U * (j + 3)];
  asm volatile(
      // Compute denominator
      "vfdotpex.s.h   %[D0],  %[cd0],  %[cd0];"
      "vfdotpex.s.h   %[D1],  %[cd1],  %[cd1];"
      "vfdotpex.s.h   %[D2],  %[cd2],  %[cd2];"
      "vfdotpex.s.h   %[D3],  %[cd3],  %[cd3];"
      // Compute numerator
      "vfdotpex.s.h   %[re0], %[ab],   %[cd0];"
      "vfdotpex.s.h   %[re1], %[ab],   %[cd1];"
      "vfdotpex.s.h   %[re2], %[ab],   %[cd2];"
      "vfdotpex.s.h   %[re3], %[ab],   %[cd3];"
      "vfdotpex.s.h   %[im0], %[ab_n], %[cd0];"
      "vfdotpex.s.h   %[im1], %[ab_n], %[cd1];"
      "vfdotpex.s.h   %[im2], %[ab_n], %[cd2];"
      "vfdotpex.s.h   %[im3], %[ab_n], %[cd3];"
      "fdiv.s         %[re0], %[re0],  %[D0];"
      "fdiv.s         %[re1], %[re1],  %[D1];"
      "fdiv.s         %[re2], %[re2],  %[D2];"
      "fdiv.s         %[re3], %[re3],  %[D3];"
      "fdiv.s         %[im0], %[im0],  %[D0];"
      "fdiv.s         %[im1], %[im1],  %[D1];"
      "fdiv.s         %[im2], %[im2],  %[D2];"
      "fdiv.s         %[im3], %[im3],  %[D3];"
      // Pack in 32b word
      "vfcpka.h.s       %[re0], %[re0], %[im0];"
      "vfcpka.h.s       %[re1], %[re1], %[im1];"
      "vfcpka.h.s       %[re2], %[re2], %[im2];"
      "vfcpka.h.s       %[re3], %[re3], %[im3];"
      : [D0] "+&r"(D0), [D1] "+&r"(D1), [D2] "+&r"(D2), [D3] "+&r"(D3),
        [re0] "+&r"(re0), [re1] "+&r"(re1), [re2] "+&r"(re2), [re3] "+&r"(re3),
        [im0] "+&r"(im0), [im1] "+&r"(im1), [im2] "+&r"(im2), [im3] "+&r"(im3)
      : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2), [cd3] "r"(cd3),
        [ab] "r"(ab), [ab_n] "r"(ab_n)
      :);
  *((uint32_t *)&pH[2 * (i * nTX + j)]) = *(uint32_t *)&re0;
  *((uint32_t *)&pH[2 * (i * nTX + j + 1)]) = *(uint32_t *)&re1;
  *((uint32_t *)&pH[2 * (i * nTX + j + 2)]) = *(uint32_t *)&re2;
  *((uint32_t *)&pH[2 * (i * nTX + j + 3)]) = *(uint32_t *)&re3;
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
void mempool_chest_f16s_unrolled4(__fp16 *pH, __fp16 *pPilotRX,
                                  __fp16 *pPilotTX, uint32_t nRX, uint32_t nTX,
                                  uint32_t nSc) {

  uint32_t ab0, ab1, ab2, ab3;
  uint32_t ab_n0, ab_n1, ab_n2, ab_n3;

  for (uint32_t k = 0; k < nSc; k++) {
    for (uint32_t i = 0; i < nRX; i++) {
      ab0 = *(uint32_t *)&pPilotRX[2U * i];
      ab1 = *(uint32_t *)&pPilotRX[2U * (i + 1)];
      ab2 = *(uint32_t *)&pPilotRX[2U * (i + 2)];
      ab3 = *(uint32_t *)&pPilotRX[2U * (i + 3)];
      asm volatile(
          "xor           %[ab_n0], %[ab0], %[neg_mask];"
          "xor           %[ab_n1], %[ab1], %[neg_mask];"
          "xor           %[ab_n2], %[ab2], %[neg_mask];"
          "xor           %[ab_n3], %[ab3], %[neg_mask];"
          "pv.shuffle2.h %[ab_n0], %[ab_n0],  %[mask];"
          "pv.shuffle2.h %[ab_n1], %[ab_n1],  %[mask];"
          "pv.shuffle2.h %[ab_n2], %[ab_n2],  %[mask];"
          "pv.shuffle2.h %[ab_n3], %[ab_n3],  %[mask];"
          : [ab_n0] "+&r"(ab_n0), [ab_n1] "+&r"(ab_n1), [ab_n2] "+&r"(ab_n2),
            [ab_n3] "+&r"(ab_n3)
          : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),
            [neg_mask] "r"(0x00008000), [mask] "r"(0x00020003)
          :);
      for (uint32_t j = 0; j < nTX; j += 4) {
        chest_unrolled4_inner_loop_f16(pPilotTX, pH, nTX, ab0, ab_n0, i, j);
        chest_unrolled4_inner_loop_f16(pPilotTX, pH, nTX, ab1, ab_n1, i + 1, j);
        chest_unrolled4_inner_loop_f16(pPilotTX, pH, nTX, ab2, ab_n2, i + 2, j);
        chest_unrolled4_inner_loop_f16(pPilotTX, pH, nTX, ab3, ab_n3, i + 3, j);
      }
    }
    pPilotTX += 2 * nTX;
    pPilotRX += 2 * nRX;
    pH += 2 * (nTX * nRX);
  }
  return;
}
