// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

// Includes inner loop
#include "mempool_chest_f16s.h"

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
void mempool_chest_f16p_unrolled4(__fp16 *pH, __fp16 *pPilotRX,
                                  __fp16 *pPilotTX, uint32_t nRX, uint32_t nTX,
                                  uint32_t nSc, uint32_t core_id,
                                  uint32_t nPE) {
  uint32_t ab0, ab1, ab2, ab3;
  uint32_t ab_n0, ab_n1, ab_n2, ab_n3;
  __fp16 *pTX;
  __fp16 *pRX;
  __fp16 *pOut;
  for (uint32_t k = core_id; k < nSc; k += nPE) {
    pTX = pPilotTX + k * (2 * nTX);
    pRX = pPilotRX + k * (2 * nRX);
    pOut = pH + k * 2 * (nTX * nRX);
    for (uint32_t i = 0; i < nRX; i += 4) {
      ab0 = *(uint32_t *)&pRX[2U * i];
      ab1 = *(uint32_t *)&pRX[2U * (i + 1)];
      ab2 = *(uint32_t *)&pRX[2U * (i + 2)];
      ab3 = *(uint32_t *)&pRX[2U * (i + 3)];
      asm volatile(
          "xor      %[ab_n0], %[ab0], %[neg_mask];"
          "xor      %[ab_n1], %[ab1], %[neg_mask];"
          "xor      %[ab_n2], %[ab2], %[neg_mask];"
          "xor      %[ab_n3], %[ab3], %[neg_mask];"
          "pv.shuffle2.h %[ab_n0], %[ab_n0],  %[mask];"
          "pv.shuffle2.h %[ab_n1], %[ab_n1],  %[mask];"
          "pv.shuffle2.h %[ab_n2], %[ab_n2],  %[mask];"
          "pv.shuffle2.h %[ab_n3], %[ab_n3],  %[mask];"
          : [ab_n0] "=&r"(ab_n0), [ab_n1] "=&r"(ab_n1), [ab_n2] "=&r"(ab_n2),
            [ab_n3] "=&r"(ab_n3)
          : [ab0] "r"(ab0), [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),
            [neg_mask] "r"(0x00008000), [mask] "r"(0x00020001)
          :);
      for (uint32_t j = 0; j < nTX; j += 4) {
        chest_unrolled4_inner_loop_f16(pTX, pOut, nTX, ab0, ab_n0, i, j);
        chest_unrolled4_inner_loop_f16(pTX, pOut, nTX, ab1, ab_n1, i + 1, j);
        chest_unrolled4_inner_loop_f16(pTX, pOut, nTX, ab2, ab_n2, i + 2, j);
        chest_unrolled4_inner_loop_f16(pTX, pOut, nTX, ab3, ab_n3, i + 3, j);
      }
    }
  }
  mempool_log_partial_barrier(2, core_id, nPE);
  return;
}
