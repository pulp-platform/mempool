// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define BITREVERSETABLE
#define ASM

void mempool_bitrevtable_q16s_riscv32(int16_t *pSrc, const uint16_t bitRevLen,
                                      const uint16_t *pBitRevTab) {
  uint16_t addr1, addr2;
  int16_t tmpa, tmpb;
  for (uint32_t i = 0; i < bitRevLen; i += 2) {
    addr1 = pBitRevTab[i] >> 2U;
    addr2 = pBitRevTab[i + 1] >> 2U;

    tmpa = pSrc[addr1];
    tmpb = pSrc[addr2];
    pSrc[addr1] = tmpb;
    pSrc[addr2] = tmpa;

    tmpa = pSrc[addr1 + 1];
    tmpb = pSrc[addr2 + 1];
    pSrc[addr1 + 1] = tmpb;
    pSrc[addr2 + 1] = tmpa;
  }
}

#ifndef ASM
#define SWAP_ITEMS                                                             \
  addr1 = *(uint32_t *)&pBitRevTab[i];                                         \
  addr2 = *(uint32_t *)&pBitRevTab[i + 2];                                     \
  addr3 = *(uint32_t *)&pBitRevTab[i + 4];                                     \
  addr4 = *(uint32_t *)&pBitRevTab[i + 6];                                     \
  addr1 = __SRA2(*(v2s *)&addr1, *(v2s *)&s2);                                 \
  addr2 = __SRA2(*(v2s *)&addr2, *(v2s *)&s2);                                 \
  addr3 = __SRA2(*(v2s *)&addr3, *(v2s *)&s2);                                 \
  addr4 = __SRA2(*(v2s *)&addr4, *(v2s *)&s2);                                 \
  a1 = addr1[1];                                                               \
  a2 = addr2[1];                                                               \
  a3 = addr3[1];                                                               \
  a4 = addr4[1];                                                               \
  b1 = addr1[0];                                                               \
  b2 = addr2[0];                                                               \
  b3 = addr3[0];                                                               \
  b4 = addr4[0];                                                               \
  tmpa1 = *(uint32_t *)&pSrc[a1];                                              \
  tmpa2 = *(uint32_t *)&pSrc[a2];                                              \
  tmpa3 = *(uint32_t *)&pSrc[a3];                                              \
  tmpa4 = *(uint32_t *)&pSrc[a4];                                              \
  tmpb1 = *(uint32_t *)&pSrc[b1];                                              \
  tmpb2 = *(uint32_t *)&pSrc[b2];                                              \
  tmpb3 = *(uint32_t *)&pSrc[b3];                                              \
  tmpb4 = *(uint32_t *)&pSrc[b4];                                              \
  *((uint32_t *)&pSrc[a1]) = tmpb1;                                            \
  *((uint32_t *)&pSrc[a2]) = tmpb2;                                            \
  *((uint32_t *)&pSrc[a3]) = tmpb3;                                            \
  *((uint32_t *)&pSrc[a4]) = tmpb4;                                            \
  *((uint32_t *)&pSrc[b1]) = tmpa1;                                            \
  *((uint32_t *)&pSrc[b2]) = tmpa2;                                            \
  *((uint32_t *)&pSrc[b3]) = tmpa3;                                            \
  *((uint32_t *)&pSrc[b4]) = tmpa4;
#else
#define SWAP_ITEMS                                                             \
  addr1 = *(uint32_t *)&pBitRevTab[i];                                         \
  addr2 = *(uint32_t *)&pBitRevTab[i + 2];                                     \
  addr3 = *(uint32_t *)&pBitRevTab[i + 4];                                     \
  addr4 = *(uint32_t *)&pBitRevTab[i + 6];                                     \
  asm volatile("pv.sra.h  %[addr1],%[addr1],%[s2];"                            \
               "pv.sra.h  %[addr2],%[addr2],%[s2];"                            \
               "pv.sra.h  %[addr3],%[addr3],%[s2];"                            \
               "pv.sra.h  %[addr4],%[addr4],%[s2];"                            \
               "pv.extract.h  %[a1],%[addr1],1;"                               \
               "pv.extract.h  %[a2],%[addr2],1;"                               \
               "pv.extract.h  %[a3],%[addr3],1;"                               \
               "pv.extract.h  %[a4],%[addr4],1;"                               \
               "pv.extract.h  %[b1],%[addr1],0;"                               \
               "pv.extract.h  %[b2],%[addr2],0;"                               \
               "pv.extract.h  %[b3],%[addr3],0;"                               \
               "pv.extract.h  %[b4],%[addr4],0;"                               \
               : [a1] "=r"(a1), [a2] "=r"(a2), [a3] "=r"(a3), [a4] "=r"(a4),   \
                 [b1] "=r"(b1), [b2] "=r"(b2), [b3] "=r"(b3), [b4] "=r"(b4),   \
                 [addr1] "+&r"(addr1), [addr2] "+&r"(addr2),                   \
                 [addr3] "+&r"(addr3), [addr4] "+&r"(addr4)                    \
               : [s2] "r"(s2)                                                  \
               :);                                                             \
  tmpa1 = *(uint32_t *)&pSrc[a1];                                              \
  tmpa2 = *(uint32_t *)&pSrc[a2];                                              \
  tmpa3 = *(uint32_t *)&pSrc[a3];                                              \
  tmpa4 = *(uint32_t *)&pSrc[a4];                                              \
  tmpb1 = *(uint32_t *)&pSrc[b1];                                              \
  tmpb2 = *(uint32_t *)&pSrc[b2];                                              \
  tmpb3 = *(uint32_t *)&pSrc[b3];                                              \
  tmpb4 = *(uint32_t *)&pSrc[b4];                                              \
  *((uint32_t *)&pSrc[a1]) = tmpb1;                                            \
  *((uint32_t *)&pSrc[a2]) = tmpb2;                                            \
  *((uint32_t *)&pSrc[a3]) = tmpb3;                                            \
  *((uint32_t *)&pSrc[a4]) = tmpb4;                                            \
  *((uint32_t *)&pSrc[b1]) = tmpa1;                                            \
  *((uint32_t *)&pSrc[b2]) = tmpa2;                                            \
  *((uint32_t *)&pSrc[b3]) = tmpa3;                                            \
  *((uint32_t *)&pSrc[b4]) = tmpa4;
#endif

void mempool_bitrevtable_q16s_xpulpimg(int16_t *pSrc, const uint16_t bitRevLen,
                                       const uint16_t *pBitRevTab) {
  uint32_t addr1, addr2, addr3, addr4;
  uint32_t s2 = 0x00020002;
  uint32_t tmpa1, tmpa2, tmpa3, tmpa4;
  uint32_t tmpb1, tmpb2, tmpb3, tmpb4;
  int32_t a1, a2, a3, a4;
  int32_t b1, b2, b3, b4;
  for (uint32_t i = 0; i < bitRevLen; i += 8) {
    SWAP_ITEMS;
  }
}

void mempool_bitrevtable_q16p_xpulpimg(int16_t *pSrc, const uint16_t bitRevLen,
                                       const uint16_t *pBitRevTab,
                                       const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t addr1, addr2, addr3, addr4;
  uint32_t s2 = 0x00020002;
  uint32_t tmpa1, tmpa2, tmpa3, tmpa4;
  uint32_t tmpb1, tmpb2, tmpb3, tmpb4;
  int32_t a1, a2, a3, a4;
  int32_t b1, b2, b3, b4;
  for (uint32_t i = 8 * core_id; i < bitRevLen; i += (8 * nPE)) {
    SWAP_ITEMS;
  }
  mempool_log_partial_barrier(2, core_id, nPE);
}

void mempool_bitrev_q16p_xpulpimg(int16_t *pSrc, int16_t *pDst,
                                  const uint16_t fftLen, const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t idx_result, idx, i, j;
  for (i = core_id; i < fftLen; i += nPE) {
    idx_result = 0;
    idx = i;
    for (j = 0; j < LOG2; j++) {
      idx_result = (idx_result << 1U) | (idx & 1U);
      idx = idx >> 1U;
    }
    pDst[2 * idx_result] = pSrc[2 * i];
    pDst[2 * idx_result + 1] = pSrc[2 * i + 1];
  }
  mempool_log_partial_barrier(2, core_id, nPE);
}
