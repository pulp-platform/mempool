// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

static void mempool_cfft_q16p(uint16_t fftLen, int16_t *pTwiddle,
                              uint16_t *pBitRevTable, int16_t *pSrc,
                              uint16_t bitReverseLen, uint8_t ifftFlag,
                              uint8_t bitReverseFlag, uint32_t nPE);

static void mempool_cfft_radix4by2_q16p(int16_t *pSrc, uint32_t fftLen,
                                        const int16_t *pCoef, uint32_t nPE);

void mempool_cfft_q16p(uint16_t fftLen, int16_t *pTwiddle,
                       uint16_t *pBitRevTable, int16_t *pSrc,
                       uint16_t bitReverseLen, uint8_t ifftFlag,
                       uint8_t bitReverseFlag, uint32_t nPE) {

  if (ifftFlag == 0) {
    switch (fftLen) {
    case 16:
    case 64:
    case 256:
    case 1024:
    case 4096:
      mempool_radix4_butterfly_q16p_xpulpimg(pSrc, fftLen, pTwiddle, 1U, nPE);
      break;
    case 32:
    case 128:
    case 512:
    case 2048:
      mempool_cfft_radix4by2_q16p(pSrc, fftLen, pTwiddle, nPE);
      break;
    }
  }

  if (bitReverseFlag) {
#ifndef BITREVERSETABLE
    mempool_bitrev_q16p_xpulpimg((uint16_t *)pSrc, (uint16_t *)pDst, fftLen,
                                 nPE);
#else
    mempool_bitrev_q16p_xpulpimg((uint16_t *)pSrc, bitReverseLen, pBitRevTable,
                                 nPE);
#endif
  }
}

/* When the number of elements is not a power of four the first step must be a
 * radix 2 butterfly */
void mempool_cfft_radix4by2_q16p(int16_t *pSrc, uint32_t fftLen,
                                 const int16_t *pCoef, uint32_t nPE) {

  uint32_t i;
  uint32_t n2, step;
  v2s pa, pb;

  uint32_t l;
  v2s CoSi;
  v2s a, b, t;
  int16_t testa, testb;
  uint32_t core_id = mempool_get_core_id();

  n2 = fftLen >> 1;
  step = (n2 + nPE - 1) / nPE;
  for (i = core_id * step; i < MIN(core_id * step + step, n2); i++) {

    CoSi = *(v2s *)&pCoef[i * 2];
    l = i + n2;
    a = __SRA2(*(v2s *)&pSrc[2 * i], ((v2s){1, 1}));
    b = __SRA2(*(v2s *)&pSrc[2 * l], ((v2s){1, 1}));
    t = __SUB2(a, b);
    *((v2s *)&pSrc[i * 2]) = __SRA2(__ADD2(a, b), ((v2s){1, 1}));

    testa = (int16_t)(__DOTP2(t, CoSi) >> 16);
    testb = (int16_t)(__DOTP2(t, __PACK2(-CoSi[1], CoSi[0])) >> 16);
    *((v2s *)&pSrc[l * 2]) = __PACK2(testa, testb);
  }
  mempool_log_barrier(2, core_id);

  if (nPE > 1) {
    if (core_id < nPE / 2) {
      // first col
      mempool_radix4_butterfly_q16p_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U,
                                             nPE / 2);
    } else {
      // second col
      mempool_radix4_butterfly_q16p_xpulpimg(
          pSrc + fftLen, n2, (int16_t *)pCoef, 2U, nPE - nPE / 2);
    }
  } else {
    // first col
    mempool_radix4_butterfly_q16p_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U, nPE);
    // second col
    mempool_radix4_butterfly_q16p_xpulpimg(pSrc + fftLen, n2, (int16_t *)pCoef,
                                           2U, nPE);
  }

  for (i = core_id * step; i < MIN(core_id * step + step, n2); i++) {

    pa = *(v2s *)&pSrc[4 * i];
    pb = *(v2s *)&pSrc[4 * i + 2];

    pa = __SLL2(pa, ((v2s){1, 1}));
    pb = __SLL2(pb, ((v2s){1, 1}));

    *((v2s *)&pSrc[4 * i]) = pa;
    *((v2s *)&pSrc[4 * i + 2]) = pb;
  }
  mempool_log_barrier(2, core_id);
}
