// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

static void mempool_cfft_q16s(uint16_t fftLen, int16_t *pTwiddle,
                              uint16_t *pBitRevTable, int16_t *pSrc,
                              uint16_t bitReverseLen, uint8_t ifftFlag,
                              uint8_t bitReverseFlag);

static void mempool_cfft_radix4by2_q16s(int16_t *pSrc, uint32_t fftLen,
                                        const int16_t *pCoef);

#ifndef XPULP

void mempool_cfft_q16s(uint16_t fftLen, int16_t *pTwiddle,
                       uint16_t *pBitRevTable, int16_t *pSrc,
                       uint16_t bitReverseLen, uint8_t ifftFlag,
                       uint8_t bitReverseFlag) {

  if (ifftFlag == 0) {
    switch (fftLen) {
    case 16:
    case 64:
    case 256:
    case 1024:
    case 4096:
      mempool_radix4_butterfly_q16s_riscv32(pSrc, fftLen, pTwiddle, 1);
      break;
    case 32:
    case 128:
    case 512:
    case 2048:
      mempool_cfft_radix4by2_q16s(pSrc, fftLen, pTwiddle);
      break;
    }
  }

  if (bitReverseFlag)
    mempool_bitrev_q16s_riscv32((uint16_t *)pSrc, bitReverseLen, pBitRevTable);
}

void mempool_cfft_radix4by2_q16s(int16_t *pSrc, uint32_t fftLen,
                                 const int16_t *pCoef) {

  uint32_t i;
  uint32_t n2;
  int16_t p0, p1, p2, p3;

  uint32_t l;
  int16_t xt, yt, cosVal, sinVal;

  n2 = fftLen >> 1;

  for (i = 0; i < n2; i++) {
    cosVal = pCoef[i * 2];
    sinVal = pCoef[(i * 2) + 1];

    l = i + n2;

    xt = (int16_t)((pSrc[2 * i] >> 1U) - (pSrc[2 * l] >> 1U));
    pSrc[2 * i] = (int16_t)(((pSrc[2 * i] >> 1U) + (pSrc[2 * l] >> 1U)) >> 1U);

    yt = (int16_t)((pSrc[2 * i + 1] >> 1U) - (pSrc[2 * l + 1] >> 1U));
    pSrc[2 * i + 1] =
        (int16_t)(((pSrc[2 * l + 1] >> 1U) + (pSrc[2 * i + 1] >> 1U)) >> 1U);

    pSrc[2U * l] = (int16_t)(((int16_t)(((int32_t)xt * cosVal) >> 16)) +
                             ((int16_t)(((int32_t)yt * sinVal) >> 16)));

    pSrc[2U * l + 1U] = (int16_t)(((int16_t)(((int32_t)yt * cosVal) >> 16)) -
                                  ((int16_t)(((int32_t)xt * sinVal) >> 16)));
  }

  // first col
  mempool_radix4_butterfly_q16s_riscv32(pSrc, n2, (int16_t *)pCoef, 2U);
  // second col
  mempool_radix4_butterfly_q16s_riscv32(pSrc + fftLen, n2, (int16_t *)pCoef,
                                        2U);

  for (i = 0; i < (fftLen >> 1); i++) {
    p0 = pSrc[4 * i + 0];
    p1 = pSrc[4 * i + 1];
    p2 = pSrc[4 * i + 2];
    p3 = pSrc[4 * i + 3];

    p0 = (int16_t)(p0 << 1U);
    p1 = (int16_t)(p1 << 1U);
    p2 = (int16_t)(p2 << 1U);
    p3 = (int16_t)(p3 << 1U);

    pSrc[4 * i + 0] = p0;
    pSrc[4 * i + 1] = p1;
    pSrc[4 * i + 2] = p2;
    pSrc[4 * i + 3] = p3;
  }
}

#else //#ifdef XPULP

void mempool_cfft_q16s(uint16_t fftLen, int16_t *pTwiddle,
                       uint16_t *pBitRevTable, int16_t *pSrc,
                       uint16_t bitReverseLen, uint8_t ifftFlag,
                       uint8_t bitReverseFlag) {

  if (ifftFlag == 0) {
    switch (fftLen) {
    case 16:
    case 64:
    case 256:
    case 1024:
    case 4096:
      mempool_radix4_butterfly_q16s_xpulpimg(pSrc, fftLen, pTwiddle, 1);
      break;
    case 32:
    case 128:
    case 512:
    case 2048:
      mempool_cfft_radix4by2_q16s(pSrc, fftLen, pTwiddle);
      break;
    }
  }

  if (bitReverseFlag)
    mempool_bitrev_q16s_xpulpimg((uint16_t *)pSrc, bitReverseLen, pBitRevTable);
}

void mempool_cfft_radix4by2_q16s(int16_t *pSrc, uint32_t fftLen,
                                 const int16_t *pCoef) {

  uint32_t i;
  uint32_t n2;
  v2s pa, pb;

  uint32_t l;
  v2s CoSi;
  v2s a, b, t;
  int16_t testa, testb;

  n2 = fftLen >> 1;

  for (i = 0; i < n2; i++) {
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

  // first col
  mempool_radix4_butterfly_q16s_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U);
  // second col
  mempool_radix4_butterfly_q16s_xpulpimg(pSrc + fftLen, n2, (int16_t *)pCoef,
                                         2U);

  for (i = 0; i < (fftLen >> 1); i++) {
    pa = *(v2s *)&pSrc[4 * i];
    pb = *(v2s *)&pSrc[4 * i + 2];

    pa = __SLL2(pa, ((v2s){1, 1}));
    pb = __SLL2(pb, ((v2s){1, 1}));

    *((v2s *)&pSrc[4 * i]) = pa;
    *((v2s *)&pSrc[4 * i + 2]) = pb;
  }
}

#endif
