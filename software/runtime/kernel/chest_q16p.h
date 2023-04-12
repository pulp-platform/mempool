// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

// Includes inner loop
#include "chest_q16s.h"

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
void mempool_chest_q16p_unrolled4_xpulpv2(int16_t *volatile pH,
                                          int16_t *volatile pPilotRX,
                                          int16_t *volatile pPilotTX,
                                          uint32_t nRX, uint32_t nTX,
                                          uint32_t nSc, uint32_t core_id,
                                          uint32_t nPE) {

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  int16_t *volatile pTX;
  int16_t *volatile pRX;
  int16_t *volatile pOut;

  for (uint32_t k = core_id; k < nSc; k += nPE) {
    pTX = &(*pPilotTX) + k * (2 * nTX);
    pRX = &(*pPilotRX) + k * (2 * nRX);
    pOut = &(*pH) + k * 2 * (nTX * nRX);
    for (uint32_t i = 0; i < nRX; i += 4) {
      ab0 = *(v2s *)&pRX[2U * i];
      ab1 = *(v2s *)&pRX[2U * (i + 1)];
      ab2 = *(v2s *)&pRX[2U * (i + 2)];
      ab3 = *(v2s *)&pRX[2U * (i + 3)];
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
        inner_loop(pTX, pOut, nTX, ab0, ab_n0, i, j);
        inner_loop(pTX, pOut, nTX, ab1, ab_n1, i + 1, j);
        inner_loop(pTX, pOut, nTX, ab2, ab_n2, i + 2, j);
        inner_loop(pTX, pOut, nTX, ab3, ab_n3, i + 3, j);
      }
    }
  }
  // dump_x(core_id);
  mempool_barrier(nPE);
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
void mempool_chest_q16p_unrolled4_xpulpv2_local(int16_t *volatile pH,
                                                int16_t *volatile pPilotRX,
                                                int16_t *volatile pPilotTX,
                                                uint32_t nRX, uint32_t nTX,
                                                uint32_t nSc,
                                                uint32_t core_id) {

  v2s ab;
  v2s ab_n;
  int16_t *volatile pTX;
  int16_t *volatile pRX;
  int16_t *volatile pOut;
  for (uint32_t idx = core_id * 4; idx < (nSc * nRX * nTX); idx += 1024) {

    uint32_t k = idx / (nRX * nTX);
    uint32_t i = (idx % (nRX * nTX)) / nTX;
    uint32_t j = (idx % (nRX * nTX)) % nTX;
    pTX = &(*pPilotTX) + k * (2 * nTX);
    pRX = &(*pPilotRX) + k * (2 * nRX);
    pOut = &(*pH) + k * 2 * (nTX * nRX);
    ab = *(v2s *)&pRX[2U * i];

    ab = *(v2s *)&pRX[2U * i];
    asm volatile(
        "pv.sub.h      %[ab_n], %[zero], %[ab];"
        "pv.shuffle2.h %[ab_n], %[ab],  %[mask];"
        : [ab_n] "=&r"(ab_n)
        : [ab] "r"(ab), [zero] "r"((v2s){0, 0}), [mask] "r"((v2s){0x1, 0x2})
        :);
    inner_loop(pTX, pOut, nTX, ab, ab_n, i, j);
  }
  // dump_x(core_id);
  mempool_log_partial_barrier(2, core_id, N_SAMPLES);
  return;
}
