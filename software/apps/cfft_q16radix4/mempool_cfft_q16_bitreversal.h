// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifndef BITREVTABLE
static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            uint16_t *pDst,
                                            const uint16_t fftLen,
                                            const uint32_t nPE);
#else
static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab,
                                            const uint32_t nPE);
#endif

static void mempool_bitrev_q16s_riscv32(    uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab);

static void mempool_bitrev_q16s_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab);

#ifndef BITREVERSETABLE
static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            uint16_t *pDst,
                                            const uint16_t fftLen,
                                            const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t result, n;
  uint32_t i;
  for (i = core_id; i < fftLen; i += nPE) {
      n = i + fftLen;
      result = 0;
      while (n > 0) {
          if (result != 0)
            result = result << 1;
          if ((n & 1) == 1)
            result = result ^ 1;
          n = n >> 1U;
      }
      result = (result >> 1);
      *((uint32_t*)&pDst[2 * result]) = (uint32_t) pSrc[2 * i];
  }
  pSrc = pDst;
  mempool_log_partial_barrier(2, core_id, nPE);
}
#else
static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab,
                                            const uint32_t nPE) {
    uint32_t i;
    uint32_t core_id = mempool_get_core_id();
    v2s addr1, addr2, addr3, addr4;
    v2s s2 = (v2s){ 2, 2 };
    v2s tmpa1, tmpa2, tmpa3, tmpa4;
    v2s tmpb1, tmpb2, tmpb3, tmpb4;
    int32_t a1, a2, a3, a4;
    int32_t b1, b2, b3, b4;
    for (i = 8 * core_id; i < bitRevLen; i += (8 * nPE)){
        #ifndef ASM
        addr1 = *(v2s *)&pBitRevTab[i];
        addr2 = *(v2s *)&pBitRevTab[i + 2];
        addr3 = *(v2s *)&pBitRevTab[i + 4];
        addr4 = *(v2s *)&pBitRevTab[i + 6];
        addr1 = __SRA2(addr1, s2);
        addr2 = __SRA2(addr2, s2);
        addr3 = __SRA2(addr3, s2);
        addr4 = __SRA2(addr4, s2);
        a1 = addr1[0];
        a2 = addr2[0];
        a3 = addr3[0];
        a4 = addr4[0];
        b1 = addr1[1];
        b2 = addr2[1];
        b3 = addr3[1];
        b4 = addr4[1];
        tmpa1 = *(v2s *)&pSrc[a1];
        tmpa2 = *(v2s *)&pSrc[a2];
        tmpa3 = *(v2s *)&pSrc[a3];
        tmpa4 = *(v2s *)&pSrc[a4];
        tmpb1 = *(v2s *)&pSrc[b1];
        tmpb2 = *(v2s *)&pSrc[b2];
        tmpb3 = *(v2s *)&pSrc[b3];
        tmpb4 = *(v2s *)&pSrc[b4];
        *((v2s *)&pSrc[a1]) = tmpb1;
        *((v2s *)&pSrc[a2]) = tmpb2;
        *((v2s *)&pSrc[a3]) = tmpb3;
        *((v2s *)&pSrc[a4]) = tmpb4;
        *((v2s *)&pSrc[b1]) = tmpa1;
        *((v2s *)&pSrc[b2]) = tmpa2;
        *((v2s *)&pSrc[b3]) = tmpa3;
        *((v2s *)&pSrc[b4]) = tmpa4;
        #else
        addr1 = *(v2s *)&pBitRevTab[i];
        addr2 = *(v2s *)&pBitRevTab[i + 2];
        addr3 = *(v2s *)&pBitRevTab[i + 4];
        addr4 = *(v2s *)&pBitRevTab[i + 6];
        asm volatile (
            "pv.sra.h  %[addr1],%[addr1],%[s2];"
            "pv.sra.h  %[addr2],%[addr2],%[s2];"
            "pv.sra.h  %[addr3],%[addr3],%[s2];"
            "pv.sra.h  %[addr4],%[addr4],%[s2];"
            "pv.extract.h  %[a1],%[addr1],0;"
            "pv.extract.h  %[a2],%[addr2],0;"
            "pv.extract.h  %[a3],%[addr3],0;"
            "pv.extract.h  %[a4],%[addr4],0;"
            "pv.extract.h  %[b1],%[addr1],1;"
            "pv.extract.h  %[b2],%[addr2],1;"
            "pv.extract.h  %[b3],%[addr3],1;"
            "pv.extract.h  %[b4],%[addr4],1;"
            : [a1] "=r" (a1), [a2] "=r" (a2), [a3] "=r" (a3), [a4] "=r" (a4),
              [b1] "=r" (b1), [b2] "=r" (b2), [b3] "=r" (b3), [b4] "=r" (b4),
              [addr1] "+r" (addr1), [addr2] "+r" (addr2), [addr3] "+r" (addr3), [addr4] "+r" (addr4)
            : [s2] "r" (s2)
            : );
        tmpa1 = *(v2s *)&pSrc[a1];
        tmpa2 = *(v2s *)&pSrc[a2];
        tmpa3 = *(v2s *)&pSrc[a3];
        tmpa4 = *(v2s *)&pSrc[a4];
        tmpb1 = *(v2s *)&pSrc[b1];
        tmpb2 = *(v2s *)&pSrc[b2];
        tmpb3 = *(v2s *)&pSrc[b3];
        tmpb4 = *(v2s *)&pSrc[b4];
        *((v2s *)&pSrc[a1]) = tmpb1;
        *((v2s *)&pSrc[a2]) = tmpb2;
        *((v2s *)&pSrc[a3]) = tmpb3;
        *((v2s *)&pSrc[a4]) = tmpb4;
        *((v2s *)&pSrc[b1]) = tmpa1;
        *((v2s *)&pSrc[b2]) = tmpa2;
        *((v2s *)&pSrc[b3]) = tmpa3;
        *((v2s *)&pSrc[b4]) = tmpa4;
        #endif
    }
    mempool_log_partial_barrier(2, core_id, nPE);
}
#endif

static void mempool_bitrev_q16s_riscv32(  uint16_t *pSrc,
                                          const uint16_t bitRevLen,
                                          const uint16_t *pBitRevTab) {
    uint16_t addr1, addr2;
    uint16_t tmpa, tmpb;
    for (uint32_t i = 0; i < bitRevLen; i += 2) {
      addr1 = pBitRevTab[i] >> 2U;
      addr2 = pBitRevTab[i + 1] >> 2U;
      tmpa = pSrc[addr1];
      tmpb = pSrc[addr2];
      pSrc[addr1] = tmpb;
      pSrc[addr2] = tmpa;
    }
}

static void mempool_bitrev_q16s_xpulpimg( uint16_t *pSrc,
                                          const uint16_t bitRevLen,
                                          const uint16_t *pBitRevTab) {
    v2s addr0, addr1, tmpa, tmpb;
    int16_t a00, a01, a10, a11;

    for (uint32_t i = 0; i < bitRevLen; i += 4) {

      addr0 = *(v2s *)&pBitRevTab[i];
      addr1 = *(v2s *)&pBitRevTab[i + 2];
      a00 = addr0[0] >> 2;
      a01 = addr0[1] >> 2;
      a10 = addr1[0] >> 2;
      a11 = addr1[1] >> 2;
      tmpa = *(v2s *)&pSrc[ a00 ];
      tmpb = *(v2s *)&pSrc[ a01 ];
      *((v2s *)&pSrc[ a00 ]) = tmpb;
      *((v2s *)&pSrc[ a01 ]) = tmpa;
      tmpa = *(v2s *)&pSrc[ a10 ];
      tmpb = *(v2s *)&pSrc[ a11 ];
      *((v2s *)&pSrc[ a10 ]) = tmpb;
      *((v2s *)&pSrc[ a11 ]) = tmpa;

    }
}

