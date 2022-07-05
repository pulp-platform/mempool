// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab,
                                            const uint32_t nPE);

static void mempool_bitrev_q16s_riscv32(    uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab);

static void mempool_bitrev_q16s_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab);



static void mempool_bitrev_q16p_xpulpimg(   uint16_t *pSrc,
                                            const uint16_t bitRevLen,
                                            const uint16_t *pBitRevTab,
                                            const uint32_t nPE) {
    uint32_t i;
    uint32_t core_id = mempool_get_core_id();
    v2s addr, tmpa, tmpb;
    for (i = 2 * core_id; i < bitRevLen; i += (2 * nPE)){
      addr = __SRA2(*(v2s *)&pBitRevTab[i], ((v2s){ 2, 2 }));
      tmpa = *(v2s *)&pSrc[ addr[0] ];
      tmpb = *(v2s *)&pSrc[ addr[1] ];
      *((v2s *)&pSrc[ addr[0] ]) = tmpb;
      *((v2s *)&pSrc[ addr[1] ]) = tmpa;
    }
    mempool_log_partial_barrier(2, core_id, nPE);
}

static void mempool_bitrev_q16s_riscv32(  uint16_t *pSrc,
                                          const uint16_t bitRevLen,
                                          const uint16_t *pBitRevTab) {
    v2s addr, tmpa, tmpb;
    for (uint32_t i = 0; i < bitRevLen; i += 2) {
      addr = *(v2s *)&pBitRevTab[i] >> 2;
      tmpa = *(v2s *)&pSrc[ addr[0] ];
      tmpb = *(v2s *)&pSrc[ addr[1] ];
      *((v2s *)&pSrc[ addr[0] ]) = tmpb;
      *((v2s *)&pSrc[ addr[1] ]) = tmpa;
    }
}

static void mempool_bitrev_q16s_xpulpimg( uint16_t *pSrc,
                                          const uint16_t bitRevLen,
                                          const uint16_t *pBitRevTab) {
    v2s addr, tmpa, tmpb;
    for (uint32_t i = 0; i < bitRevLen; i += 2) {
      addr = *(v2s *)&pBitRevTab[i] >> 2;
      tmpa = *(v2s *)&pSrc[ addr[0] ];
      tmpb = *(v2s *)&pSrc[ addr[1] ];
      *((v2s *)&pSrc[ addr[0] ]) = tmpb;
      *((v2s *)&pSrc[ addr[1] ]) = tmpa;
    }
}

