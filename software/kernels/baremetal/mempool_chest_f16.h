// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define __CDOTP
#define __MUL

/* a[i] = ar[i] + i * ai[j]

   out[i][j] = a[i] / c[j]
   out[i][j + 1] = a[i] / c[j + 1h
   out[i][j + 2] = a[i] / c[j + 2]
   out[i][j + 3] = a[i] / c[j + 3]*/

#ifdef __XDIVSQRT
#define DIV_LOOP(ab, ab_n, i)                                                  \
  {                                                                            \
    re0 = 0;                                                                   \
    re1 = 0;                                                                   \
    re2 = 0;                                                                   \
    re3 = 0;                                                                   \
    im0 = 0;                                                                   \
    im1 = 0;                                                                   \
    im2 = 0;                                                                   \
    im3 = 0;                                                                   \
    D0 = 0;                                                                    \
    D1 = 0;                                                                    \
    D2 = 0;                                                                    \
    D3 = 0;                                                                    \
    cd0 = *(uint32_t *)&pPilotTX_itr[2U * j];                                  \
    cd1 = *(uint32_t *)&pPilotTX_itr[2U * (j + 1)];                            \
    cd2 = *(uint32_t *)&pPilotTX_itr[2U * (j + 2)];                            \
    cd3 = *(uint32_t *)&pPilotTX_itr[2U * (j + 3)];                            \
    asm volatile("vfdotpex.s.h   %[D0],  %[cd0], %[cd0];"                      \
                 "vfdotpex.s.h   %[D1],  %[cd1], %[cd1];"                      \
                 "vfdotpex.s.h   %[D2],  %[cd2], %[cd2];"                      \
                 "vfdotpex.s.h   %[D3],  %[cd3], %[cd3];"                      \
                 "vfdotpex.s.h   %[re0], %[x],   %[cd0];"                      \
                 "vfdotpex.s.h   %[re1], %[x],   %[cd1];"                      \
                 "vfdotpex.s.h   %[re2], %[x],   %[cd2];"                      \
                 "vfdotpex.s.h   %[re3], %[x],   %[cd3];"                      \
                 "vfdotpex.s.h   %[im0], %[y],   %[cd0];"                      \
                 "vfdotpex.s.h   %[im1], %[y],   %[cd1];"                      \
                 "vfdotpex.s.h   %[im2], %[y],   %[cd2];"                      \
                 "vfdotpex.s.h   %[im3], %[y],   %[cd3];"                      \
                 "fdiv.s         %[re0], %[re0], %[D0];"                       \
                 "fdiv.s         %[re1], %[re1], %[D1];"                       \
                 "fdiv.s         %[re2], %[re2], %[D2];"                       \
                 "fdiv.s         %[re3], %[re3], %[D3];"                       \
                 "fdiv.s         %[im0], %[im0], %[D0];"                       \
                 "fdiv.s         %[im1], %[im1], %[D1];"                       \
                 "fdiv.s         %[im2], %[im2], %[D2];"                       \
                 "fdiv.s         %[im3], %[im3], %[D3];"                       \
                 "vfcpka.h.s     %[re0], %[re0], %[im0];"                      \
                 "vfcpka.h.s     %[re1], %[re1], %[im1];"                      \
                 "vfcpka.h.s     %[re2], %[re2], %[im2];"                      \
                 "vfcpka.h.s     %[re3], %[re3], %[im3];"                      \
                 : [D0] "+&r"(D0), [D1] "+&r"(D1), [D2] "+&r"(D2),             \
                   [D3] "+&r"(D3), [re0] "+&r"(re0), [re1] "+&r"(re1),         \
                   [re2] "+&r"(re2), [re3] "+&r"(re3), [im0] "+&r"(im0),       \
                   [im1] "+&r"(im1), [im2] "+&r"(im2), [im3] "+&r"(im3)        \
                 : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2),             \
                   [cd3] "r"(cd3), [x] "r"(ab), [y] "r"(ab_n)                  \
                 :);                                                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j)]) = re0;                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 1)]) = re1;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 2)]) = re2;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 3)]) = re3;                       \
  }
#else
#define DIV_LOOP(ab, ab_n, i)                                                  \
  {                                                                            \
    re0 = 0;                                                                   \
    re1 = 0;                                                                   \
    re2 = 0;                                                                   \
    re3 = 0;                                                                   \
    im0 = 0;                                                                   \
    im1 = 0;                                                                   \
    im2 = 0;                                                                   \
    im3 = 0;                                                                   \
    D0 = 0;                                                                    \
    D1 = 0;                                                                    \
    D2 = 0;                                                                    \
    D3 = 0;                                                                    \
    cd0 = *(uint32_t *)&pPilotTX_itr[2U * j];                                  \
    cd1 = *(uint32_t *)&pPilotTX_itr[2U * (j + 1)];                            \
    cd2 = *(uint32_t *)&pPilotTX_itr[2U * (j + 2)];                            \
    cd3 = *(uint32_t *)&pPilotTX_itr[2U * (j + 3)];                            \
    asm volatile("vfdotpex.s.h   %[D0],  %[cd0], %[cd0];"                      \
                 "vfdotpex.s.h   %[D1],  %[cd1], %[cd1];"                      \
                 "vfdotpex.s.h   %[D2],  %[cd2], %[cd2];"                      \
                 "vfdotpex.s.h   %[D3],  %[cd3], %[cd3];"                      \
                 "vfdotpex.s.h   %[re0], %[x],   %[cd0];"                      \
                 "vfdotpex.s.h   %[re1], %[x],   %[cd1];"                      \
                 "vfdotpex.s.h   %[re2], %[x],   %[cd2];"                      \
                 "vfdotpex.s.h   %[re3], %[x],   %[cd3];"                      \
                 "vfdotpex.s.h   %[im0], %[y],   %[cd0];"                      \
                 "vfdotpex.s.h   %[im1], %[y],   %[cd1];"                      \
                 "vfdotpex.s.h   %[im2], %[y],   %[cd2];"                      \
                 "vfdotpex.s.h   %[im3], %[y],   %[cd3];"                      \
                 : [D0] "+&r"(D0), [D1] "+&r"(D1), [D2] "+&r"(D2),             \
                   [D3] "+&r"(D3), [re0] "+&r"(re0), [re1] "+&r"(re1),         \
                   [re2] "+&r"(re2), [re3] "+&r"(re3), [im0] "+&r"(im0),       \
                   [im1] "+&r"(im1), [im2] "+&r"(im2), [im3] "+&r"(im3)        \
                 : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2),             \
                   [cd3] "r"(cd3), [x] "r"(ab), [y] "r"(ab_n)                  \
                 :);                                                           \
    re0 = re0 / D0;                                                            \
    re1 = re1 / D1;                                                            \
    re2 = re2 / D2;                                                            \
    re3 = re3 / D3;                                                            \
    im0 = im0 / D0;                                                            \
    im1 = im1 / D1;                                                            \
    im2 = im2 / D2;                                                            \
    im3 = im3 / D3;                                                            \
    asm volatile("vfcpka.h.s %[re0], %[re0], %[im0];"                          \
                 "vfcpka.h.s %[re1], %[re1], %[im1];"                          \
                 "vfcpka.h.s %[re2], %[re2], %[im2];"                          \
                 "vfcpka.h.s %[re3], %[re3], %[im3];"                          \
                 : [re0] "+&r"(re0), [re1] "+&r"(re1), [re2] "+&r"(re2),       \
                   [re3] "+&r"(re3), [im0] "+&r"(im0), [im1] "+&r"(im1),       \
                   [im2] "+&r"(im2), [im3] "+&r"(im3)                          \
                 : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2),             \
                   [cd3] "r"(cd3), [x] "r"(ab), [y] "r"(ab_n)                  \
                 :);                                                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j)]) = re0;                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 1)]) = re1;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 2)]) = re2;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 3)]) = re3;                       \
  }
#endif

/* a[i] = ar[i] + i * ai[j]

   out[i][j] = a[i] * c[j]
   out[i][j + 1] = a[i] * c[j + 1]
   out[i][j + 2] = a[i] * c[j + 2]
   out[i][j + 3] = a[i] * c[j + 3]*/

#define MUL_LOOP(ab, ab_n, i)                                                  \
  {                                                                            \
    re0 = 0;                                                                   \
    re1 = 0;                                                                   \
    re2 = 0;                                                                   \
    re3 = 0;                                                                   \
    im0 = 0;                                                                   \
    im1 = 0;                                                                   \
    im2 = 0;                                                                   \
    im3 = 0;                                                                   \
    cd0 = *(uint32_t *)&pPilotTX_itr[2U * j];                                  \
    cd1 = *(uint32_t *)&pPilotTX_itr[2U * (j + 1)];                            \
    cd2 = *(uint32_t *)&pPilotTX_itr[2U * (j + 2)];                            \
    cd3 = *(uint32_t *)&pPilotTX_itr[2U * (j + 3)];                            \
    asm volatile("vfdotpex.s.h   %[re0], %[x], %[cd0];"                        \
                 "vfdotpex.s.h   %[re1], %[x], %[cd1];"                        \
                 "vfdotpex.s.h   %[re2], %[x], %[cd2];"                        \
                 "vfdotpex.s.h   %[re3], %[x], %[cd3];"                        \
                 "vfdotpex.s.h   %[im0], %[y], %[cd0];"                        \
                 "vfdotpex.s.h   %[im1], %[y], %[cd1];"                        \
                 "vfdotpex.s.h   %[im2], %[y], %[cd2];"                        \
                 "vfdotpex.s.h   %[im3], %[y], %[cd3];"                        \
                 : [re0] "+&r"(re0), [re1] "+&r"(re1), [re2] "+&r"(re2),       \
                   [re3] "+&r"(re3), [im0] "+&r"(im0), [im1] "+&r"(im1),       \
                   [im2] "+&r"(im2), [im3] "+&r"(im3)                          \
                 : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2),             \
                   [cd3] "r"(cd3), [x] "r"(ab), [y] "r"(ab_n)                  \
                 :);                                                           \
    asm volatile(                                                              \
        "vfcpka.h.s       %[re0], %[re0], %[im0];"                             \
        "vfcpka.h.s       %[re1], %[re1], %[im1];"                             \
        "vfcpka.h.s       %[re2], %[re2], %[im2];"                             \
        "vfcpka.h.s       %[re3], %[re3], %[im3];"                             \
        : [re0] "+&r"(re0), [re1] "+&r"(re1), [re2] "+&r"(re2),                \
          [re3] "+&r"(re3), [im0] "+&r"(im0), [im1] "+&r"(im1),                \
          [im2] "+&r"(im2), [im3] "+&r"(im3)                                   \
        : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2), [cd3] "r"(cd3)       \
        :);                                                                    \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j)]) = re0;                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 1)]) = re1;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 2)]) = re2;                       \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 3)]) = re3;                       \
  }

#define CMUL_LOOP(ab, i)                                                       \
  {                                                                            \
    sum0 = 0;                                                                  \
    sum1 = 0;                                                                  \
    sum2 = 0;                                                                  \
    sum3 = 0;                                                                  \
    cd0 = *(uint32_t *)&pPilotTX_itr[2U * j];                                  \
    cd1 = *(uint32_t *)&pPilotTX_itr[2U * (j + 1)];                            \
    cd2 = *(uint32_t *)&pPilotTX_itr[2U * (j + 2)];                            \
    cd3 = *(uint32_t *)&pPilotTX_itr[2U * (j + 3)];                            \
    asm volatile("fcdotpex.s.h   %[sum0], %[x], %[cd0];"                       \
                 "fcdotpex.s.h   %[sum1], %[x], %[cd1];"                       \
                 "fcdotpex.s.h   %[sum2], %[x], %[cd2];"                       \
                 "fcdotpex.s.h   %[sum3], %[x], %[cd3];"                       \
                 : [sum0] "+&r"(sum0), [sum1] "+&r"(sum1), [sum2] "+&r"(sum2), \
                   [sum3] "+&r"(sum3)                                          \
                 : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2),             \
                   [cd3] "r"(cd3), [x] "r"(ab)                                 \
                 :);                                                           \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j)]) = sum0;                          \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 1)]) = sum1;                      \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 2)]) = sum2;                      \
    *((uint32_t *)&pH_itr[2 * (i * nTX + j + 3)]) = sum3;                      \
  }

#define SHUFFLE_A                                                              \
  {                                                                            \
    asm volatile(                                                              \
        "xor           %[ab_n0], %[ab0],   %[neg_mask];"                       \
        "xor           %[ab_n1], %[ab1],   %[neg_mask];"                       \
        "xor           %[ab_n2], %[ab2],   %[neg_mask];"                       \
        "xor           %[ab_n3], %[ab3],   %[neg_mask];"                       \
        "pv.shuffle2.h %[ab_n0], %[ab_n0], %[mask];"                           \
        "pv.shuffle2.h %[ab_n1], %[ab_n1], %[mask];"                           \
        "pv.shuffle2.h %[ab_n2], %[ab_n2], %[mask];"                           \
        "pv.shuffle2.h %[ab_n3], %[ab_n3], %[mask];"                           \
        : [ab_n0] "+&r"(ab_n0), [ab_n1] "+&r"(ab_n1), [ab_n2] "+&r"(ab_n2),    \
          [ab_n3] "+&r"(ab_n3)                                                 \
        : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),      \
          [neg_mask] "r"(0x00008000), [mask] "r"(0x00020003)                   \
        :);                                                                    \
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
  uint32_t cd0, cd1, cd2, cd3;
  uint32_t re0, re1, re2, re3;
  uint32_t im0, im1, im2, im3;
  uint32_t D0, D1, D2, D3;
  uint32_t ab_n0, ab_n1, ab_n2, ab_n3;
  __fp16 *pPilotTX_itr;
  __fp16 *pPilotRX_itr;
  __fp16 *pH_itr;

  for (uint32_t k = 0; k < nSc; k++) {
    pPilotTX_itr = pPilotTX + k * (2 * nTX);
    pPilotRX_itr = pPilotRX + k * (2 * nRX);
    pH_itr = pH + k * 2 * (nTX * nRX);
    for (uint32_t i = 0; i < nRX; i++) {
      ab0 = *(uint32_t *)&pPilotRX_itr[2U * i];
      ab1 = *(uint32_t *)&pPilotRX_itr[2U * (i + 1)];
      ab2 = *(uint32_t *)&pPilotRX_itr[2U * (i + 2)];
      ab3 = *(uint32_t *)&pPilotRX_itr[2U * (i + 3)];
      SHUFFLE_A;
      for (uint32_t j = 0; j < nTX; j += 4) {
        DIV_LOOP(ab0, ab_n0, i);
        DIV_LOOP(ab1, ab_n1, i + 1);
        DIV_LOOP(ab2, ab_n2, i + 2);
        DIV_LOOP(ab3, ab_n3, i + 3);
      }
    }
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
  @param[in]     core_id ID of the PE
  @param[in]     nPE Number of PEs
  @return        none
*/
void mempool_chest_f16p_unrolled4(__fp16 *pH, __fp16 *pPilotRX,
                                  __fp16 *pPilotTX, uint32_t nRX, uint32_t nTX,
                                  uint32_t nSc, uint32_t core_id,
                                  uint32_t nPE) {
  uint32_t ab0, ab1, ab2, ab3;
  uint32_t cd0, cd1, cd2, cd3;
#ifndef __CDOTP
  uint32_t ab_n0, ab_n1, ab_n2, ab_n3;
  uint32_t re0, re1, re2, re3;
  uint32_t im0, im1, im2, im3;
#else
  uint32_t sum0, sum1, sum2, sum3;
#endif

#ifndef __MUL
  uint32_t D0, D1, D2, D3;
#endif

  __fp16 *pPilotTX_itr;
  __fp16 *pPilotRX_itr;
  __fp16 *pH_itr;

  for (uint32_t k = core_id; k < nSc; k += nPE) {
    pPilotTX_itr = pPilotTX + k * (2 * nTX);
    pPilotRX_itr = pPilotRX + k * (2 * nRX);
    pH_itr = pH + k * 2 * (nTX * nRX);
    for (uint32_t i = 0; i < nRX; i += 4) {
      ab0 = *(uint32_t *)&pPilotRX_itr[2U * i];
      ab1 = *(uint32_t *)&pPilotRX_itr[2U * (i + 1)];
      ab2 = *(uint32_t *)&pPilotRX_itr[2U * (i + 2)];
      ab3 = *(uint32_t *)&pPilotRX_itr[2U * (i + 3)];
#ifndef __CDOTP
      SHUFFLE_A;
#endif

      for (uint32_t j = 0; j < nTX; j += 4) {
#if (defined(__CDOTP) && defined(__MUL))
        CMUL_LOOP(ab0, i);
        CMUL_LOOP(ab1, i + 1);
        CMUL_LOOP(ab2, i + 2);
        CMUL_LOOP(ab3, i + 3);
#elif (!defined(__CDOTP) && defined(__MUL))
        MUL_LOOP(ab0, ab_n0, i);
        MUL_LOOP(ab1, ab_n1, i + 1);
        MUL_LOOP(ab2, ab_n2, i + 2);
        MUL_LOOP(ab3, ab_n3, i + 3);
#else
        DIV_LOOP(ab0, ab_n0, i)
        DIV_LOOP(ab1, ab_n1, i + 1)
        DIV_LOOP(ab2, ab_n2, i + 2)
        DIV_LOOP(ab3, ab_n3, i + 3)
#endif
      }
    }
  }
  return;
}

void mempool_chest_f16p_unrolled4_local(__fp16 *volatile pH,
                                        __fp16 *volatile pPilotRX,
                                        __fp16 *volatile pPilotTX, uint32_t nRX,
                                        uint32_t nTX, uint32_t nSc,
                                        uint32_t core_id, uint32_t nPE) {
  uint32_t ab0, ab1, ab2, ab3;
  uint32_t cd0, cd1, cd2, cd3;
  uint32_t sum0, sum1, sum2, sum3;
  __fp16 *pPilotTX_itr;
  __fp16 *pPilotRX_itr;
  __fp16 *pH_itr;
  uint32_t itr, i, j;

  // Cores Loop over the received pilots vector
  for (itr = core_id * 4; itr < (nSc * nRX);
       itr += (BANKING_FACTOR * NUM_CORES)) {
    // Received pilots are aligned to cores
    uint32_t sc_RX = itr / nRX;
    pPilotTX_itr = pPilotTX + sc_RX * (2 * nTX);
    pPilotRX_itr = pPilotRX + sc_RX * (2 * nRX);
    pH_itr = pH + sc_RX * 2 * (nTX * nRX);

    // Load received pilots
    i = itr % nRX;
    ab0 = *(uint32_t *)&pPilotRX_itr[2U * i];
    ab1 = *(uint32_t *)&pPilotRX_itr[2U * (i + 1)];
    ab2 = *(uint32_t *)&pPilotRX_itr[2U * (i + 2)];
    ab3 = *(uint32_t *)&pPilotRX_itr[2U * (i + 3)];
    for (j = 0; j < nTX; j += 4) {
      CMUL_LOOP(ab0, i);
      CMUL_LOOP(ab1, i + 1);
      CMUL_LOOP(ab2, i + 2);
      CMUL_LOOP(ab3, i + 3);
    }
  }
  mempool_barrier(nPE);
  return;
}
