// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifdef FOLDED_TWIDDLES
static int16_t* mempool_cfft_q16p_folded(uint16_t fftLen, int16_t  *pCoef_src,
                                     int16_t  *pCoef_dst, uint16_t *pBitRevTable,
                                     int16_t  *pSrc16, int16_t  *pDst16,
                                     uint16_t bitReverseLen, uint8_t ifftFlag,
                                     uint8_t bitReverseFlag, uint32_t nPE);
#else
static int16_t* mempool_cfft_q16p_folded(uint16_t fftLen, int16_t *pCoef_src,
                                     uint16_t *pBitRevTable, int16_t  *pSrc16,
                                     int16_t  *pDst16, uint16_t bitReverseLen,
                                     uint8_t ifftFlag, uint8_t bitReverseFlag,
                                     uint32_t nPE);
#endif

#ifdef FOLDED_TWIDDLES
static int16_t* mempool_cfft_q16p_folded(uint16_t fftLen, int16_t  *pCoef_src,
                                     int16_t  *pCoef_dst, uint16_t *pBitRevTable,
                                     int16_t  *pSrc16, int16_t  *pDst16,
                                     uint16_t bitReverseLen, uint8_t ifftFlag,
                                     uint8_t bitReverseFlag, uint32_t nPE)

#else
static int16_t* mempool_cfft_q16p_folded(uint16_t fftLen, int16_t *pCoef,
                                     uint16_t *pBitRevTable, int16_t  *pSrc16,
                                     int16_t  *pDst16, uint16_t bitReverseLen,
                                     uint8_t ifftFlag, uint8_t bitReverseFlag,
                                     uint32_t nPE)
#endif
{

  int16_t *pTmp;
  if (ifftFlag == 0) {
    #ifdef FOLDED_TWIDDLES
    pTmp = mempool_butterfly_q16p_folded(pSrc16, pDst16, fftLen, pCoef_src, pCoef_dst, nPE);
    #else
    pTmp = mempool_butterfly_q16p_folded(pSrc16, pDst16, fftLen, pCoef, nPE);
    #endif
  }

  if (bitReverseFlag) {
    #ifndef BITREVERSETABLE
    if (pTmp == pDst16) {
      pDst16 = pSrc16;
      pSrc16 = pTmp;
    }
    mempool_bitrev_q16p_xpulpimg((uint16_t *)pSrc16, (uint16_t *)pDst16, fftLen, nPE);
    #else
    if (pTmp == pSrc16)
      pDst16 = pSrc16;
    mempool_bitrev_q16p_xpulpimg((uint16_t *)pDst16, bitReverseLen, pBitRevTable, nPE);
    #endif
  }
  return pDst16;

}
