// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifdef TWIDDLE_MODIFIER
static void mempool_cfft_memsized_q16p(   uint16_t fftLen,
                                          int16_t *pCoef_src,
                                          uint16_t *pBitRevTable,
                                          int16_t *pSrc16,
                                          int16_t *pDst16,
                                          uint16_t bitReverseLen,
                                          uint8_t ifftFlag,
                                          uint8_t bitReverseFlag,
                                          uint32_t nPE);
#else
static void mempool_cfft_memsized_q16p(   uint16_t fftLen,
                                          int16_t *pCoef_src,
                                          int16_t *pCoef_dst,
                                          uint16_t *pBitRevTable,
                                          int16_t *pSrc16,
                                          int16_t *pDst16,
                                          uint16_t bitReverseLen,
                                          uint8_t ifftFlag,
                                          uint8_t bitReverseFlag,
                                          uint32_t nPE);
#endif

#ifdef TWIDDLE_MODIFIER
static void mempool_cfft_memsized_q16p(   uint16_t fftLen,
                                          int16_t *pCoef,
                                          uint16_t *pBitRevTable,
                                          int16_t *pSrc16,
                                          int16_t *pDst16,
                                          uint16_t bitReverseLen,
                                          uint8_t ifftFlag,
                                          uint8_t bitReverseFlag,
                                          uint32_t nPE)
#else
static void mempool_cfft_memsized_q16p(   uint16_t fftLen,
                                          int16_t *pCoef_src,
                                          int16_t *pCoef_dst,
                                          uint16_t *pBitRevTable,
                                          int16_t *pSrc16,
                                          int16_t *pDst16,
                                          uint16_t bitReverseLen,
                                          uint8_t ifftFlag,
                                          uint8_t bitReverseFlag,
                                          uint32_t nPE)
#endif
{
    if (ifftFlag == 0) {
        switch (fftLen) {
        case 16:
        case 64:
        case 256:
        case 1024:
        case 4096:
            #ifdef TWIDDLE_MODIFIER
            mempool_memsized_butterfly(pSrc16, pDst16, fftLen, pCoef, nPE);
            #else
            mempool_memsized_butterfly(pSrc16, pDst16, fftLen, pCoef_src, pCoef_dst, nPE);
            #endif
            break;
        case 32:
        case 128:
        case 512:
        case 2048:
            // TODO
            break;
        }
    }
    if (bitReverseFlag) {
        #ifndef BITREVERSETABLE
        mempool_bitrev_q16p_xpulpimg((uint16_t *)pSrc16, (uint16_t *)pDst16, fftLen, nPE);
        #else
        mempool_bitrev_q16p_xpulpimg((uint16_t *)pSrc16, bitReverseLen, pBitRevTable, nPE);
        #endif
    }
}
