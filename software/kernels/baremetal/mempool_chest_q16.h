// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"
#define __MUL

/* a[i] = ar[i] + i * ai[j]
   out[i][j] = a[i] / c[j]
   out[i][j + 1] = a[i] / c[j + 1]
   out[i][j + 2] = a[i] / c[j + 2]
   out[i][j + 3] = a[i] / c[j + 3]*/

#define DIV_LOOP(ab, ab_n)                                                     \
  {                                                                            \
    cd0 = *(v2s *)&pPilotTX_itr[2U * j];                                       \
    cd1 = *(v2s *)&pPilotTX_itr[2U * (j + 1)];                                 \
    cd2 = *(v2s *)&pPilotTX_itr[2U * (j + 2)];                                 \
    cd3 = *(v2s *)&pPilotTX_itr[2U * (j + 3)];                                 \
    D0 = (1 << 16U) / __DOTP2(cd0, cd0);                                       \
    D1 = (1 << 16U) / __DOTP2(cd1, cd1);                                       \
    D2 = (1 << 16U) / __DOTP2(cd2, cd2);                                       \
    D3 = (1 << 16U) / __DOTP2(cd3, cd3);                                       \
    re0 = __DOTP2(ab, cd0);                                                    \
    re1 = __DOTP2(ab, cd1);                                                    \
    re2 = __DOTP2(ab, cd2);                                                    \
    re3 = __DOTP2(ab, cd3);                                                    \
    im0 = __DOTP2(ab_n, cd0);                                                  \
    im1 = __DOTP2(ab_n, cd1);                                                  \
    im2 = __DOTP2(ab_n, cd2);                                                  \
    im3 = __DOTP2(ab_n, cd3);                                                  \
    re0 = __CLIP((re0 * D0) >> 8, 16);                                         \
    re1 = __CLIP((re1 * D1) >> 8, 16);                                         \
    re2 = __CLIP((re2 * D2) >> 8, 16);                                         \
    re3 = __CLIP((re3 * D3) >> 8, 16);                                         \
    im0 = __CLIP((im0 * D0) >> 8, 16);                                         \
    im1 = __CLIP((im1 * D1) >> 8, 16);                                         \
    im2 = __CLIP((im2 * D2) >> 8, 16);                                         \
    im3 = __CLIP((im3 * D3) >> 8, 16);                                         \
    re0 = (int32_t)(__PACK2(im0, re0));                                        \
    re1 = (int32_t)(__PACK2(im1, re1));                                        \
    re2 = (int32_t)(__PACK2(im2, re2));                                        \
    re3 = (int32_t)(__PACK2(im3, re3));                                        \
  }

/* a[i] = ar[i] + i * ai[j]
   out[i][j] = a[i] * c[j]
   out[i][j + 1] = a[i] * c[j + 1]
   out[i][j + 2] = a[i] * c[j + 2]
   out[i][j + 3] = a[i] * c[j + 3]*/

#define MUL_LOOP(ab, ab_n)                                                     \
  {                                                                            \
    cd0 = *(v2s *)&pPilotTX_itr[2U * j];                                       \
    cd1 = *(v2s *)&pPilotTX_itr[2U * (j + 1)];                                 \
    cd2 = *(v2s *)&pPilotTX_itr[2U * (j + 2)];                                 \
    cd3 = *(v2s *)&pPilotTX_itr[2U * (j + 3)];                                 \
    re0 = __DOTP2(ab_n, cd0);                                                  \
    re1 = __DOTP2(ab_n, cd1);                                                  \
    re2 = __DOTP2(ab_n, cd2);                                                  \
    re3 = __DOTP2(ab_n, cd3);                                                  \
    im0 = __DOTP2(ab, cd0);                                                    \
    im1 = __DOTP2(ab, cd1);                                                    \
    im2 = __DOTP2(ab, cd2);                                                    \
    im3 = __DOTP2(ab, cd3);                                                    \
    re0 = __CLIP(re0 >> 8, 16);                                                \
    re1 = __CLIP(re1 >> 8, 16);                                                \
    re2 = __CLIP(re2 >> 8, 16);                                                \
    re3 = __CLIP(re3 >> 8, 16);                                                \
    im0 = __CLIP(im0 >> 8, 16);                                                \
    im1 = __CLIP(im1 >> 8, 16);                                                \
    im2 = __CLIP(im2 >> 8, 16);                                                \
    im3 = __CLIP(im3 >> 8, 16);                                                \
    re0 = (int32_t)(__PACK2(im0, re0));                                        \
    re1 = (int32_t)(__PACK2(im1, re1));                                        \
    re2 = (int32_t)(__PACK2(im2, re2));                                        \
    re3 = (int32_t)(__PACK2(im3, re3));                                        \
  }

#define STORE_OUT(idx_row, idx_col)                                            \
  {                                                                            \
    *((v2s *)&pH_itr[2 * (idx_row * nTX + idx_col)]) = (v2s)re0;               \
    *((v2s *)&pH_itr[2 * (idx_row * nTX + idx_col + 1)]) = (v2s)re1;           \
    *((v2s *)&pH_itr[2 * (idx_row * nTX + idx_col + 2)]) = (v2s)re2;           \
    *((v2s *)&pH_itr[2 * (idx_row * nTX + idx_col + 3)]) = (v2s)re3;           \
  }

#ifdef __MUL
#define SHUFFLE_A                                                              \
  {                                                                            \
    asm volatile(                                                              \
        "pv.sub.h      %[ab_n0], %[zero], %[ab0];"                             \
        "pv.sub.h      %[ab_n1], %[zero], %[ab1];"                             \
        "pv.sub.h      %[ab_n2], %[zero], %[ab2];"                             \
        "pv.sub.h      %[ab_n3], %[zero], %[ab3];"                             \
        "pv.shuffle2.h %[ab0], %[ab0],  %[mask];"                              \
        "pv.shuffle2.h %[ab1], %[ab1],  %[mask];"                              \
        "pv.shuffle2.h %[ab2], %[ab2],  %[mask];"                              \
        "pv.shuffle2.h %[ab3], %[ab3],  %[mask];"                              \
        : [ab_n0] "=&r"(ab_n0), [ab_n1] "=&r"(ab_n1), [ab_n2] "=&r"(ab_n2),    \
          [ab_n3] "=&r"(ab_n3)                                                 \
        : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),      \
          [zero] "r"(0x00000000), [mask] "r"(0x00020001)                       \
        :);                                                                    \
    ab_n0[1] = ab0[0];                                                         \
    ab_n1[1] = ab1[0];                                                         \
    ab_n2[1] = ab2[0];                                                         \
    ab_n3[1] = ab3[0];                                                         \
  }
#else
#define SHUFFLE_A                                                              \
  {                                                                            \
    asm volatile(                                                              \
        "pv.sub.h      %[ab_n0], %[zero], %[ab0];"                             \
        "pv.sub.h      %[ab_n1], %[zero], %[ab1];"                             \
        "pv.sub.h      %[ab_n2], %[zero], %[ab2];"                             \
        "pv.sub.h      %[ab_n3], %[zero], %[ab3];"                             \
        "pv.shuffle2.h %[ab_n0], %[ab_n0],  %[mask];"                          \
        "pv.shuffle2.h %[ab_n1], %[ab_n1],  %[mask];"                          \
        "pv.shuffle2.h %[ab_n2], %[ab_n2],  %[mask];"                          \
        "pv.shuffle2.h %[ab_n3], %[ab_n3],  %[mask];"                          \
        : [ab_n0] "=&r"(ab_n0), [ab_n1] "=&r"(ab_n1), [ab_n2] "=&r"(ab_n2),    \
          [ab_n3] "=&r"(ab_n3)                                                 \
        : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),      \
          [zero] "r"(0x00000000), [mask] "r"(0x00020001)                       \
        :);                                                                    \
    ab_n0[1] = ab0[0];                                                         \
    ab_n1[1] = ab1[0];                                                         \
    ab_n2[1] = ab2[0];                                                         \
    ab_n3[1] = ab3[0];                                                         \
  }
#endif

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

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  v2s cd0, cd1, cd2, cd3;
  int32_t re0, re1, re2, re3;
  int32_t im0, im1, im2, im3;
#ifndef __MUL
  int32_t D0, D1, D2, D3;
#endif

  uint32_t i, j, k;

  int16_t *pPilotTX_itr;
  int16_t *pPilotRX_itr;
  int16_t *pH_itr;
  for (k = 0; k < nSc; k++) {
    pPilotTX_itr = pPilotTX + k * (2 * nTX);
    pPilotRX_itr = pPilotRX + k * (2 * nRX);
    pH_itr = pH + k * 2 * (nTX * nRX);
    for (i = 0; i < nRX; i += 4) {
      ab0 = *(v2s *)&pPilotRX_itr[2U * i];
      ab1 = *(v2s *)&pPilotRX_itr[2U * (i + 1)];
      ab2 = *(v2s *)&pPilotRX_itr[2U * (i + 2)];
      ab3 = *(v2s *)&pPilotRX_itr[2U * (i + 3)];
      SHUFFLE_A;
      for (j = 0; j < nTX; j += 4) {
#ifdef __MUL
        MUL_LOOP(ab0, ab_n0);
        *((v2s *)&pH_itr[2 * (i * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab1, ab_n1);
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab2, ab_n2);
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab3, ab_n3);
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 3)]) = (v2s)re3;
#else
        DIV_LOOP(ab0, ab_n0);
        *((v2s *)&pH_itr[2 * (i * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab1, ab_n1);
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab2, ab_n2);
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab3, ab_n3);
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 3)]) = (v2s)re3;
#endif
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
  @return        none
*/
void mempool_chest_q16p_unrolled4(int16_t *volatile pH,
                                  int16_t *volatile pPilotRX,
                                  int16_t *volatile pPilotTX, uint32_t nRX,
                                  uint32_t nTX, uint32_t nSc, uint32_t core_id,
                                  uint32_t nPE) {

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  v2s cd0, cd1, cd2, cd3;
  int32_t re0, re1, re2, re3;
  int32_t im0, im1, im2, im3;
#ifndef __MUL
  int32_t D0, D1, D2, D3;
#endif

  int16_t *pPilotTX_itr;
  int16_t *pPilotRX_itr;
  int16_t *pH_itr;
  for (uint32_t k = core_id; k < nSc; k += nPE) {
    pPilotTX_itr = pPilotTX + k * (2 * nTX);
    pPilotRX_itr = pPilotRX + k * (2 * nRX);
    pH_itr = pH + k * 2 * (nTX * nRX);
    for (uint32_t i = 0; i < nRX; i += 4) {
      ab0 = *(v2s *)&pPilotRX_itr[2U * i];
      ab1 = *(v2s *)&pPilotRX_itr[2U * (i + 1)];
      ab2 = *(v2s *)&pPilotRX_itr[2U * (i + 2)];
      ab3 = *(v2s *)&pPilotRX_itr[2U * (i + 3)];
      SHUFFLE_A;
      for (uint32_t j = 0; j < nTX; j += 4) {
#ifdef __MUL
        MUL_LOOP(ab0, ab_n0);
        *((v2s *)&pH_itr[2 * (i * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab1, ab_n1);
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab2, ab_n2);
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 3)]) = (v2s)re3;
        MUL_LOOP(ab3, ab_n3);
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 3)]) = (v2s)re3;
#else
        DIV_LOOP(ab0, ab_n0);
        *((v2s *)&pH_itr[2 * (i * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * (i * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab1, ab_n1);
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab2, ab_n2);
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 3)]) = (v2s)re3;
        DIV_LOOP(ab3, ab_n3);
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j)]) = (v2s)re0;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 1)]) = (v2s)re1;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 2)]) = (v2s)re2;
        *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 3)]) = (v2s)re3;
#endif
      }
    }
  }
  mempool_log_partial_barrier(2, core_id, nPE);
  return;
}

void mempool_chest_q16p_unrolled4_local(int16_t *volatile pH,
                                        int16_t *volatile pPilotRX,
                                        int16_t *volatile pPilotTX,
                                        uint32_t nRX, uint32_t nTX,
                                        uint32_t nSc, uint32_t core_id,
                                        uint32_t nPE) {
  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  v2s cd0, cd1, cd2, cd3;
  int32_t re0, re1, re2, re3;
  int32_t im0, im1, im2, im3;
  int16_t *pPilotTX_itr;
  int16_t *pPilotRX_itr;
  int16_t *pH_itr;
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
    ab0 = *(v2s *)&pPilotRX_itr[2U * i];
    ab1 = *(v2s *)&pPilotRX_itr[2U * (i + 1)];
    ab2 = *(v2s *)&pPilotRX_itr[2U * (i + 2)];
    ab3 = *(v2s *)&pPilotRX_itr[2U * (i + 3)];
    SHUFFLE_A;
    for (j = 0; j < nTX; j += 4) {
      MUL_LOOP(ab0, ab_n0);
      *((v2s *)&pH_itr[2 * (i * nTX + j)]) = (v2s)re0;
      *((v2s *)&pH_itr[2 * (i * nTX + j + 1)]) = (v2s)re1;
      *((v2s *)&pH_itr[2 * (i * nTX + j + 2)]) = (v2s)re2;
      *((v2s *)&pH_itr[2 * (i * nTX + j + 3)]) = (v2s)re3;
      MUL_LOOP(ab1, ab_n1);
      *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j)]) = (v2s)re0;
      *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 1)]) = (v2s)re1;
      *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 2)]) = (v2s)re2;
      *((v2s *)&pH_itr[2 * ((i + 1) * nTX + j + 3)]) = (v2s)re3;
      MUL_LOOP(ab2, ab_n2);
      *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j)]) = (v2s)re0;
      *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 1)]) = (v2s)re1;
      *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 2)]) = (v2s)re2;
      *((v2s *)&pH_itr[2 * ((i + 2) * nTX + j + 3)]) = (v2s)re3;
      MUL_LOOP(ab3, ab_n3);
      *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j)]) = (v2s)re0;
      *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 1)]) = (v2s)re1;
      *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 2)]) = (v2s)re2;
      *((v2s *)&pH_itr[2 * ((i + 3) * nTX + j + 3)]) = (v2s)re3;
    }
  }
  mempool_barrier(nPE);
  return;
}
