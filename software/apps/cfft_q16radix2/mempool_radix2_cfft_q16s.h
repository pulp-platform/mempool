#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define __HAL_RISCV_BUILTINS_V2_H__
#include "xpulp/builtins_v2.h"
#include "define.h"

static void mempool_radix2_cfft_q16s(   uint16_t fftLen,
                                        int16_t *pTwiddle,
                                        uint16_t *pBitRevTable,
                                        int16_t *pSrc,
                                        uint16_t bitReverseLen,
                                        uint8_t ifftFlag,
                                        uint8_t bitReverseFlag);

static void mempool_radix2_butterfly_q16s(  int16_t *pSrc16,
                                            uint32_t fftLen,
                                            int16_t *pCoef16,
                                            uint32_t twidCoefModifier);

void mempool_radix2_bitreversal_q16s(  uint16_t *pSrc,
                                      const uint16_t bitRevLen,
                                      const uint16_t *pBitRevTab);

void mempool_radix2_cfft_q16s(  uint16_t fftLen,
                                int16_t *pTwiddle,
                                uint16_t *pBitRevTable,
                                int16_t *pSrc,
                                uint16_t bitReverseLen,
                                uint8_t ifftFlag,
                                uint8_t bitReverseFlag) {
    if (ifftFlag == 0) {
      mempool_radix2_butterfly_q16s(pSrc, fftLen, pTwiddle, 1U);
    }

    if (bitReverseFlag) {
      mempool_radix2_bitreversal_q16s((uint16_t *)pSrc, bitReverseLen, pBitRevTable);
    }
}

static void mempool_radix2_butterfly_q16s(  int16_t *pSrc16,
                                            uint32_t fftLen,
                                            int16_t *pCoef16,
                                            uint32_t twidCoefModifier) {

  uint32_t i, j, k, l;
  uint32_t n1, n2, ia;
  int16_t xt, yt, cosVal, sinVal;

  // N = fftLen;
  n2 = fftLen;

  n1 = n2;
  n2 = n2 >> 1;
  ia = 0;

  for (i = 0; i < n2; i++) {

    cosVal = pCoef16[i * 2];
    sinVal = pCoef16[(i * 2) + 1];
    l = i + n2;

    xt = (int16_t) ( (pSrc16[2 * i] >> 1U) - (pSrc16[2 * l] >> 1U) );
    pSrc16[2 * i] = (int16_t) ( ((pSrc16[2 * i] >> 1U) + (pSrc16[2 * l] >> 1U)) >> 1U );
    yt = (int16_t) ( (pSrc16[2 * i + 1] >> 1U) - (pSrc16[2 * l + 1] >> 1U) );
    pSrc16[2 * i + 1] = (int16_t) ( ((pSrc16[2 * l + 1] >> 1U) + (pSrc16[2 * i + 1] >> 1U)) >> 1U );
    pSrc16[2U * l] = (int16_t) (((int16_t)(((int32_t)xt * cosVal) >> 16)) + ((int16_t)(((int32_t)yt * sinVal) >> 16)));
    pSrc16[2U * l + 1] = (int16_t) (((int16_t)(((int32_t)yt * cosVal) >> 16)) - ((int16_t)(((int32_t)xt * sinVal) >> 16)));

  }
  twidCoefModifier = twidCoefModifier << 1U;

  /* loop for stage */
  for (k = fftLen / 2; k > 2; k = k >> 1)
  {
    n1 = n2;
    n2 = n2 >> 1;
    ia = 0;

    /* loop for groups */
    for (j = 0; j < n2; j++)
    {
      cosVal = pCoef16[ia * 2];
      sinVal = pCoef16[(ia * 2) + 1];
      ia = ia + twidCoefModifier;

      /* loop for butterfly */
      for (i = j; i < fftLen; i += n1)
      {
        l = i + n2;

        xt = (int16_t) ( (pSrc16[2 * i] >> 1U) - (pSrc16[2 * l] >> 1U) );
        pSrc16[2 * i] = (int16_t) ( ((pSrc16[2 * i] >> 1U) + (pSrc16[2 * l] >> 1U)) >> 1U );
        yt = (int16_t) ( (pSrc16[2 * i + 1] >> 1U) - (pSrc16[2 * l + 1] >> 1U) );
        pSrc16[2 * i + 1] = (int16_t) ( ((pSrc16[2 * l + 1] >> 1U) + (pSrc16[2 * i + 1] >> 1U)) >> 1U );
        pSrc16[2U * l] = (int16_t) (((int16_t)(((int32_t)xt * cosVal) >> 16)) + ((int16_t)(((int32_t)yt * sinVal) >> 16)));
        pSrc16[2U * l + 1] = (int16_t) (((int16_t)(((int32_t)yt * cosVal) >> 16)) - ((int16_t)(((int32_t)xt * sinVal) >> 16)));

      } /* butterfly loop end */

    } /* groups loop end */

    twidCoefModifier = twidCoefModifier << 1U;
  } /* stages loop end */

  n1 = n2;
  n2 = n2 >> 1;
  /* loop for groups */
  for (i = 0; i < fftLen; i += n1)
  {
    l = i + n2;
    xt = (int16_t) ( (pSrc16[2 * i] >> 1U) - (pSrc16[2 * l] >> 1U) );
    pSrc16[2 * i] = (int16_t) ( ((pSrc16[2 * i] >> 1U) + (pSrc16[2 * l] >> 1U)) );
    yt = (int16_t) ( (pSrc16[2 * i + 1] >> 1U) - (pSrc16[2 * l + 1] >> 1U) );
    pSrc16[2 * i + 1] = (int16_t) ( ((pSrc16[2 * l + 1] >> 1U) + (pSrc16[2 * i + 1] >> 1U)) );
    pSrc16[2U * l] = xt;
    pSrc16[2U * l + 1] = yt;
  } /* groups loop end */

}

void mempool_radix2_bitreversal_q16s(  uint16_t *pSrc,
                                      const uint16_t bitRevLen,
                                      const uint16_t *pBitRevTab) {
    uint16_t a, b, tmp;

    for (uint32_t i = 0; i < bitRevLen; i += 2) {
        a = pBitRevTab[i] >> 2;
        b = pBitRevTab[i + 1] >> 2;

        // real
        tmp = pSrc[a];
        pSrc[a] = pSrc[b];
        pSrc[b] = tmp;

        // complex
        tmp = pSrc[a + 1];
        pSrc[a + 1] = pSrc[b + 1];
        pSrc[b + 1] = tmp;

        // i += 2;
    }
}
