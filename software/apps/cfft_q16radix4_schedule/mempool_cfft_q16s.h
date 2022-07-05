// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cfft_q16s( uint16_t fftLen,
                        int16_t *pSrc,
                        int16_t *pCoef,
                        uint16_t *pBitRevTable,
                        uint16_t bitReverseLen,
                        uint8_t bitReverseFlag);


#ifndef XPULP

static inline void radix4s_butterfly_first(int16_t* pSrc,
                            int16_t Co1,
                            int16_t Si1,
                            int16_t Co2,
                            int16_t Si2,
                            int16_t Co3,
                            int16_t Si3,
                            uint32_t i0,
                            uint32_t n2);

static inline void radix4s_butterfly(  int16_t* pSrc,
                        int16_t Co1,
                        int16_t Si1,
                        int16_t Co2,
                        int16_t Si2,
                        int16_t Co3,
                        int16_t Si3,
                        uint32_t i0,
                        uint32_t n2);

static inline void radix4s_butterfly_last( int16_t* pSrc,
                            uint32_t i0,
                            uint32_t n2);

#else

static inline void radix4s_butterfly_first(   int16_t* pSrc,
                                              v2s CoSi1,
                                              v2s CoSi2,
                                              v2s CoSi3,
                                              uint32_t i0,
                                              uint32_t n2);

static inline void radix4s_butterfly( int16_t* pSrc,
                                      v2s CoSi1,
                                      v2s CoSi2,
                                      v2s CoSi3,
                                      uint32_t i0,
                                      uint32_t n2);

static inline void radix4s_butterfly_last(    int16_t* pSrc,
                                              uint32_t i0,
                                              uint32_t n2);

#endif

void mempool_cfft_q16s( uint16_t fftLen,
                        int16_t *pSrc,
                        int16_t *pCoef,
                        uint16_t *pBitRevTable,
                        uint16_t bitReverseLen,
                        uint8_t bitReverseFlag) {

    /* Initializations for the first stage */
    uint32_t n1, n2, i0, ic, j, k, twidCoefModifier;
    #ifndef XPULP
    int16_t Co1, Si1, Co2, Si2, Co3, Si3;
    #else
    v2s CoSi1, CoSi2, CoSi3;
    #endif

    /* FIRST STAGE */
    n1 = fftLen;
    n2 = n1 >> 2U;
    for(i0 = 0; i0 < n2; i0++) {

        #ifndef XPULP
        Co1 = pCoef[i0 * 2U];
        Si1 = pCoef[(i0 * 2U) + 1];
        Co2 = pCoef[2U * i0 * 2U];
        Si2 = pCoef[(2U * i0 * 2U) + 1];
        Co3 = pCoef[3U * (i0 * 2U)];
        Si3 = pCoef[(3U * (i0 * 2U)) + 1];
        for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
            radix4s_butterfly_first(  pSrc + idx_fft * 2 * N_BANKS_SINGLE,
                                      Co1, Si1, Co2, Si2, Co3, Si3, i0, n2);
        }
        #else
        CoSi1 = *(v2s *)&pCoef[2U * i0];
        CoSi2 = *(v2s *)&pCoef[2U * i0 * 2U];
        CoSi3 = *(v2s *)&pCoef[2U * i0 * 3U];
        for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
            radix4s_butterfly_first(  pSrc + idx_fft * 2 * N_BANKS_SINGLE,
                                      CoSi1, CoSi2, CoSi3, i0, n2);
        }
        #endif

    }

    /* MIDDLE STAGE */
    twidCoefModifier = 4;
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {
        n1 = n2;
        n2 >>= 2U;
        ic = 0U;
        for (j = 0U; j <= (n2 - 1U); j++) {

            #ifndef XPULP
            Co1 = pCoef[ic * 2U];
            Si1 = pCoef[(ic * 2U) + 1U];
            Co2 = pCoef[2U * (ic * 2U)];
            Si2 = pCoef[(2U * (ic * 2U)) + 1U];
            Co3 = pCoef[3U * (ic * 2U)];
            Si3 = pCoef[(3U * (ic * 2U)) + 1U];
            ic = ic + twidCoefModifier;
            for (i0 = j; i0 < fftLen; i0 += n1) {
                for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
                    radix4s_butterfly(  pSrc + idx_fft * 2 * N_BANKS_SINGLE,
                                        Co1, Si1, Co2, Si2, Co3, Si3, i0, n2);
                }
            }
            #else
            CoSi1 = *(v2s *)&pCoef[2U * ic];
            CoSi2 = *(v2s *)&pCoef[2U * ic * 2U];
            CoSi3 = *(v2s *)&pCoef[2U * ic * 3U];
            ic = ic + twidCoefModifier;
            for (i0 = j; i0 < fftLen; i0 += n1) {
                for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
                    radix4s_butterfly(  pSrc + idx_fft * 2 * N_BANKS_SINGLE,
                                        CoSi1, CoSi2, CoSi3, i0, n2);
                }
            }
            #endif

        }
        twidCoefModifier <<= 2U;
    }

    /* LAST STAGE */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = 0U; i0 <= (fftLen - n1); i0 += n1) {
        for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
            radix4s_butterfly_last(  pSrc + idx_fft * 2 * N_BANKS_SINGLE, i0, n2);
        }
    }

    /* BITREVERSAL */
    if(bitReverseFlag) {
        uint16_t a, b, tmp;
        uint16_t *ptr = (uint16_t*) pSrc;
        for (i0 = 0; i0 < bitReverseLen; i0 += 2) {
            for(uint32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
                a = pBitRevTable[i0] >> 2;
                b = pBitRevTable[i0 + 1] >> 2;
                // real
                tmp = (uint16_t) ptr[a];
                ptr[a] = ptr[b];
                *(uint16_t*)&ptr[b] = tmp;
                // complex
                tmp = (uint16_t) ptr[a + 1];
                ptr[a + 1] = ptr[b + 1];
                *(uint16_t*)&ptr[b + 1] = tmp;
                ptr += N_BANKS_SINGLE;
            }
            ptr = (uint16_t*) pSrc;
        }
    }


}

#ifndef XPULP

static inline void radix4s_butterfly_first(   int16_t* pSrc,
                                int16_t Co1,
                                int16_t Si1,
                                int16_t Co2,
                                int16_t Si2,
                                int16_t Co3,
                                int16_t Si3,
                                uint32_t i0,
                                uint32_t n2) {

    int16_t R0, R1, S0, S1, T0, T1, U0, U1;
    uint32_t i1, i2, i3;
    int16_t out1, out2;
    /*  index calculation for the input as, */
    /*  pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 +
    * 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /* Reading i0, i0+fftLen/2 inputs */
    /* input is down scale by 4 to avoid overflow */
    /* Read ya (real), xa (imag) input */
    T0 = pSrc[i0 * 2U] >> 2U;
    T1 = pSrc[(i0 * 2U) + 1U] >> 2U;
    /* input is down scale by 4 to avoid overflow */
    /* Read yc (real), xc(imag) input */
    S0 = pSrc[i2 * 2U] >> 2U;
    S1 = pSrc[(i2 * 2U) + 1U] >> 2U;
    /* R0 = (ya + yc) */
    R0 = (int16_t) __CLIP(T0 + S0, 15);
    /* R1 = (xa + xc) */
    R1 = (int16_t) __CLIP(T1 + S1, 15);
    /* S0 = (ya - yc) */
    S0 = (int16_t) __CLIP(T0 - S0, 15);
    /* S1 = (xa - xc) */
    S1 = (int16_t) __CLIP(T1 - S1, 15);
    /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
    /* input is down scale by 4 to avoid overflow */
    /* Read yb (real), xb(imag) input */
    T0 = pSrc[i1 * 2U] >> 2U;
    T1 = pSrc[(i1 * 2U) + 1U] >> 2U;
    /* input is down scale by 4 to avoid overflow */
    /* Read yd (real), xd(imag) input */
    U0 = pSrc[i3 * 2U] >> 2U;
    U1 = pSrc[(i3 * 2U) + 1U] >> 2U;
    /* T0 = (yb + yd) */
    T0 = (int16_t) __CLIP(T0 + U0, 15);
    /* T1 = (xb + xd) */
    T1 = (int16_t) __CLIP(T1 + U1, 15);
    /*  writing the butterfly processed i0 sample */
    /* ya' = ya + yb + yc + yd */
    /* xa' = xa + xb + xc + xd */
    pSrc[i0 * 2] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
    pSrc[(i0 * 2) + 1] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
    /* R0 = (ya + yc) - (yb + yd) */
    /* R1 = (xa + xc) - (xb + xd) */
    R0 = (int16_t) __CLIP(R0 - T0, 15);
    R1 = (int16_t) __CLIP(R1 - T1, 15);
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
    /*  Reading i0+fftLen/4 */
    /* input is down scale by 4 to avoid overflow */
    /* T0 = yb, T1 =  xb */
    T0 = pSrc[i1 * 2U] >> 2;
    T1 = pSrc[(i1 * 2U) + 1] >> 2;
    /* writing the butterfly processed i0 + fftLen/4 sample */
    /* writing output(xc', yc') in little endian format */
    pSrc[i1 * 2U] = out1;
    pSrc[(i1 * 2U) + 1] = out2;
    /*  Butterfly calculations */
    /* input is down scale by 4 to avoid overflow */
    /* U0 = yd, U1 = xd */
    U0 = pSrc[i3 * 2U] >> 2;
    U1 = pSrc[(i3 * 2U) + 1] >> 2;
    /* T0 = yb-yd */
    T0 = (int16_t) __CLIP(T0 - U0, 15);
    /* T1 = xb-xd */
    T1 = (int16_t) __CLIP(T1 - U1, 15);
    /* R1 = (ya-yc) + (xb- xd),  R0 = (xa-xc) - (yb-yd)) */
    R0 = (int16_t)__CLIP((int32_t)(S0 - T1), 15);
    R1 = (int16_t)__CLIP((int32_t)(S1 + T0), 15);
    /* S1 = (ya-yc) - (xb- xd), S0 = (xa-xc) + (yb-yd)) */
    S0 = (int16_t)__CLIP(((int32_t)S0 + T1), 15);
    S1 = (int16_t)__CLIP(((int32_t)S1 - T0), 15);
    /*  Butterfly process for the i0+fftLen/2 sample */
    /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
    out1 = (int16_t)((Si1 * S1 + Co1 * S0) >> 16);
    /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
    out2 = (int16_t)((-Si1 * S0 + Co1 * S1) >> 16);
    /* writing output(xb', yb') in little endian format */
    pSrc[i2 * 2U] = out1;
    pSrc[(i2 * 2U) + 1] = out2;
    /*  Butterfly process for the i0+3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
    /* writing output(xd', yd') in little endian format */
    pSrc[i3 * 2U] = out1;
    pSrc[(i3 * 2U) + 1] = out2;
}

static inline void radix4s_butterfly( int16_t* pSrc,
                                      int16_t Co1,
                                      int16_t Si1,
                                      int16_t Co2,
                                      int16_t Si2,
                                      int16_t Co3,
                                      int16_t Si3,
                                      uint32_t i0,
                                      uint32_t n2) {

    int16_t R0, R1, S0, S1, T0, T1, U0, U1;
    uint32_t i1, i2, i3;
    int16_t out1, out2;
    /*  index calculation for the input as, */
    /*  pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 +
    * 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /*  Reading i0, i0+fftLen/2 inputs */
    /* Read ya (real), xa(imag) input */
    T0 = pSrc[i0 * 2U];
    T1 = pSrc[(i0 * 2U) + 1U];
    /* Read yc (real), xc(imag) input */
    S0 = pSrc[i2 * 2U];
    S1 = pSrc[(i2 * 2U) + 1U];
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R0 = (int16_t) __CLIP(T0 + S0, 15);
    R1 = (int16_t) __CLIP(T1 + S1, 15);
    /* S0 = (ya - yc), S1 =(xa - xc) */
    S0 = (int16_t) __CLIP(T0 - S0, 15);
    S1 = (int16_t) __CLIP(T1 - S1, 15);
    /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
    /* Read yb (real), xb(imag) input */
    T0 = pSrc[i1 * 2U];
    T1 = pSrc[(i1 * 2U) + 1U];
    /* Read yd (real), xd(imag) input */
    U0 = pSrc[i3 * 2U];
    U1 = pSrc[(i3 * 2U) + 1U];
    /* T0 = (yb + yd), T1 = (xb + xd) */
    T0 = (int16_t) __CLIP(T0 + U0, 15);
    T1 = (int16_t) __CLIP(T1 + U1, 15);
    /*  writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd */
    /* ya' = ya + yb + yc + yd */
    out1 = (int16_t)(((R0 >> 1U) + (T0 >> 1U)) >> 1U);
    out2 = (int16_t)(((R1 >> 1U) + (T1 >> 1U)) >> 1U);
    pSrc[i0 * 2U] = out1;
    pSrc[(2U * i0) + 1U] = out2;
    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
    R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
    /* (ya-yb+yc-yd)* (si2) + (xa-xb+xc-xd)* co2 */
    out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
    /* (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
    /*  Reading i0+3fftLen/4 */
    /* Read yb (real), xb(imag) input */
    T0 = pSrc[i1 * 2U];
    T1 = pSrc[(i1 * 2U) + 1U];
    /*  writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    pSrc[i1 * 2U] = out1;
    pSrc[(i1 * 2U) + 1U] = out2;
    /*  Butterfly calculations */
    /* Read yd (real), xd(imag) input */
    U0 = pSrc[i3 * 2U];
    U1 = pSrc[(i3 * 2U) + 1U];
    /* T0 = yb-yd, T1 = xb-xd */
    T0 = (int16_t) __CLIP(T0 - U0, 15);
    T1 = (int16_t) __CLIP(T1 - U1, 15);
    /* R0 = (ya-yc) + (xb- xd), R1 = (xa-xc) - (yb-yd)) */
    R0 = (int16_t)((S0 >> 1U) - (T1 >> 1U));
    R1 = (int16_t)((S1 >> 1U) + (T0 >> 1U));
    /* S0 = (ya-yc) - (xb- xd), S1 = (xa-xc) + (yb-yd)) */
    S0 = (int16_t)((S0 >> 1U) + (T1 >> 1U));
    S1 = (int16_t)((S1 >> 1U) - (T0 >> 1U));
    /*  Butterfly process for the i0+fftLen/2 sample */
    out1 = (int16_t)((Co1 * S0 + Si1 * S1) >> 16U);
    out2 = (int16_t)((-Si1 * S0 + Co1 * S1) >> 16U);
    /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
    /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
    pSrc[i2 * 2U] = out1;
    pSrc[(i2 * 2U) + 1U] = out2;
    /*  Butterfly process for the i0+3fftLen/4 sample */
    out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
    out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    pSrc[i3 * 2U] = out1;
    pSrc[(i3 * 2U) + 1U] = out2;
}

static inline void radix4s_butterfly_last(    int16_t* pSrc,
                                              uint32_t i0,
                                              uint32_t n2) {

    int16_t R0, R1, S0, S1, T0, T1, U0, U1;
    uint32_t i1, i2, i3;
    /*  index calculation for the input as, */
    /*  pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /*  Reading i0, i0+fftLen/2 inputs */
    /* Read ya (real), xa(imag) input */
    T0 = pSrc[i0 * 2U];
    T1 = pSrc[(i0 * 2U) + 1U];
    /* Read yc (real), xc(imag) input */
    S0 = pSrc[i2 * 2U];
    S1 = pSrc[(i2 * 2U) + 1U];
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R0 = (int16_t) __CLIP(T0 + S0, 15);
    R1 = (int16_t) __CLIP(T1 + S1, 15);
    /* S0 = (ya - yc), S1 = (xa - xc) */
    S0 = (int16_t) __CLIP(T0 - S0, 15);
    S1 = (int16_t) __CLIP(T1 - S1, 15);
    /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
    /* Read yb (real), xb(imag) input */
    T0 = pSrc[i1 * 2U];
    T1 = pSrc[(i1 * 2U) + 1U];
    /* Read yd (real), xd(imag) input */
    U0 = pSrc[i3 * 2U];
    U1 = pSrc[(i3 * 2U) + 1U];
    /* T0 = (yb + yd), T1 = (xb + xd)) */
    T0 = (int16_t) __CLIP(T0 + U0, 15);
    T1 = (int16_t) __CLIP(T1 + U1, 15);
    /*  writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd */
    /* ya' = ya + yb + yc + yd */
    pSrc[i0 * 2U] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
    pSrc[(i0 * 2U) + 1U] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
    R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
    /* Read yb (real), xb(imag) input */
    T0 = pSrc[i1 * 2U];
    T1 = pSrc[(i1 * 2U) + 1U];
    /*  writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd) */
    /* yc' = (ya-yb+yc-yd) */
    pSrc[i1 * 2U] = R0;
    pSrc[(i1 * 2U) + 1U] = R1;
    /* Read yd (real), xd(imag) input */
    U0 = pSrc[i3 * 2U];
    U1 = pSrc[(i3 * 2U) + 1U];
    /* T0 = (yb - yd), T1 = (xb - xd)  */
    T0 = (int16_t) __CLIP(T0 - U0, 15);
    T1 = (int16_t) __CLIP(T1 - U1, 15);
    /*  writing the butterfly processed i0 + fftLen/2 sample */
    /* xb' = (xa+yb-xc-yd) */
    /* yb' = (ya-xb-yc+xd) */
    pSrc[i2 * 2U] = (int16_t)((S0 >> 1U) + (T1 >> 1U));
    pSrc[(i2 * 2U) + 1U] = (int16_t)((S1 >> 1U) - (T0 >> 1U));
    /*  writing the butterfly processed i0 + 3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd) */
    /* yd' = (ya+xb-yc-xd) */
    pSrc[i3 * 2U] = (int16_t)((S0 >> 1U) - (T1 >> 1U));
    pSrc[(i3 * 2U) + 1U] = (int16_t)((S1 >> 1U) + (T0 >> 1U));
}

#else

static inline void radix4s_butterfly_first(   int16_t* pSrc,
                                              v2s CoSi1,
                                              v2s CoSi2,
                                              v2s CoSi3,
                                              uint32_t i0,
                                              uint32_t n2) {

    v2s A, B, C, D, E, F, G, H;
    v2s C1, C2, C3;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    C1 = __PACK2(-CoSi1[1], CoSi1[0]);
    C2 = __PACK2(-CoSi2[1], CoSi2[0]);
    C3 = __PACK2(-CoSi3[1], CoSi3[0]);

    /* index calculation for the input as, */
    /* pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /* Read yb (real), xb(imag) input */
    B = __SRA2(*(v2s *)&pSrc[i1 * 2U], ((v2s){ 2, 2 }));
    /* Read yd (real), xd(imag) input */
    D = __SRA2(*(v2s *)&pSrc[i3 * 2U], ((v2s){ 2, 2 }));
    /* Read ya (real), xa (imag) input */
    A = __SRA2(*(v2s *)&pSrc[i0 * 2U], ((v2s){ 2, 2 }));
    /* Read yc (real), xc(imag) input */
    C = __SRA2(*(v2s *)&pSrc[i2 * 2U], ((v2s){ 2, 2 }));
    /* G0 = (yb + yd), G1 = (xb + xd) */
    G = __ADD2(B, D);
    /* H0 = (yb - yd), H1 = (xb - xd) */
    H = __SUB2(B, D);
    /* E0 = (ya + yc), E1 = (xa + xc) */
    E = __ADD2(A, C);
    /* F0 = (ya - yc), F1 = (xa - xc) */
    F = __SUB2(A, C);
    t0 = (int16_t) H[0];
    t1 = (int16_t) H[1];
    A = __SRA2(E, ((v2s){ 1, 1 }));
    B = __SRA2(G, ((v2s){ 1, 1 }));
    /* C0 = (xb - xd), C1 = (yd - yb) */
    C = __PACK2(-t1, t0);
    /* D0 = (xd - xb), D1 = (yb - yd) */
    D = __PACK2(t1, -t0);
    /* E0 = (ya+yc) - (yb+yd), E1 = (xa+xc) - (xb+xd) */
    E = __SUB2(E, G);
    /* G1 = (ya-yc) + (xb-xd), G0 = (xa-xc) - (yb-yd) */
    G = __ADD2(F, C);
    /* H1 = (ya-yc) - (xb-xd), H0 = (xa-xc) + (yb-yd) */
    H = __ADD2(F, D);
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    t0 = (int16_t)(__DOTP2(CoSi2, E) >> 16U);
    t1 = (int16_t)(__DOTP2(C2, E) >> 16U);
    /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
    /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
    t2 = (int16_t)(__DOTP2(CoSi1, H) >> 16U);
    t3 = (int16_t)(__DOTP2(C1, H) >> 16U);
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    t4 = (int16_t)(__DOTP2(CoSi3, G) >> 16U);
    t5 = (int16_t)(__DOTP2(C3, G) >> 16U);
    /* ya' = ya + yb + yc + yd */
    /* xa' = xa + xb + xc + xd */
    A = __ADD2(A, B);
    E = __PACK2(t0, t1);
    F = __PACK2(t2, t3);
    G = __PACK2(t4, t5);
    *((v2s *)&pSrc[i0 * 2U]) = A;
    *((v2s *)&pSrc[i1 * 2U]) = E;
    *((v2s *)&pSrc[i2 * 2U]) = F;
    *((v2s *)&pSrc[i3 * 2U]) = G;
}

static inline void radix4s_butterfly( int16_t* pSrc,
                                      v2s CoSi1,
                                      v2s CoSi2,
                                      v2s CoSi3,
                                      uint32_t i0,
                                      uint32_t n2) {
    v2s A, B, C, D, E, F, G, H;
    v2s C1, C2, C3;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    C1 = __PACK2(-CoSi1[1], CoSi1[0]);
    C2 = __PACK2(-CoSi2[1], CoSi2[0]);
    C3 = __PACK2(-CoSi3[1], CoSi3[0]);

    /*  index calculation for the input as, */
    /*  pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 +
     * 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pSrc[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pSrc[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pSrc[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pSrc[i2 * 2U];
    /* G0 = (yb + yd), G1 = (xb + xd) */
    G = __ADD2(B, D);
    /* H0 = (yb - yd), H1 = (xb - xd) */
    H = __SUB2(B, D);
    /* E0 = (ya + yc), E1 = (xa + xc) */
    E = __ADD2(A, C);
    /* F0 = (ya - yc), F1 =(xa - xc) */
    F = __SUB2(A, C);
    G = __SRA2(G, ((v2s){ 1, 1 }));
    H = __SRA2(H, ((v2s){ 1, 1 }));
    E = __SRA2(E, ((v2s){ 1, 1 }));
    F = __SRA2(F, ((v2s){ 1, 1 }));
    t0 = (int16_t) H[0];
    t1 = (int16_t) H[1];
    /* C0 = (ya+yc) - (yb+yd), C1 = (xa+xc) - (xb+xd) */
    C = __SUB2(E, G);
    /* D0 = (ya+yc) + (yb+yd), D1 = (xa+xc) + (xb+xd) */
    D = __ADD2(E, G);
    /* A0 = (xb-xd), A1 = (yd-yb) */
    A = __PACK2(t1, -t0);
    /* B0 = (xd-xb), B1 = (yb-yd) */
    B = __PACK2(-t1, t0);
    /* xa' = xa + xb + xc + xd */
    /* ya' = ya + yb + yc + yd */
    *((v2s *)&pSrc[i0 * 2U]) = __SRA2(D, ((v2s){ 1, 1 }));
    /* E1 = (ya-yc) + (xb-xd),  E0 = (xa-xc) - (yb-yd)) */
    E = __ADD2(F, A);
    /* F1 = (ya-yc) - (xb-xd), F0 = (xa-xc) + (yb-yd)) */
    F = __ADD2(F, B);
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    t0 = (int16_t)(__DOTP2(CoSi2, C) >> 16U);
    t1 = (int16_t)(__DOTP2(C2, C) >> 16U);
    /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
    /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
    t2 = (int16_t)(__DOTP2(CoSi1, F) >> 16U);
    t3 = (int16_t)(__DOTP2(C1, F) >> 16U);
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    t4 = (int16_t)(__DOTP2(CoSi3, E) >> 16U);
    t5 = (int16_t)(__DOTP2(C3, E) >> 16U);
    A = __PACK2(t0, t1);
    B = __PACK2(t2, t3);
    C = __PACK2(t4, t5);
    *((v2s *)&pSrc[i1 * 2U]) = A;
    *((v2s *)&pSrc[i2 * 2U]) = B;
    *((v2s *)&pSrc[i3 * 2U]) = C;
}

static inline void radix4s_butterfly_last(    int16_t* pSrc,
                                              uint32_t i0,
                                              uint32_t n2) {
    v2s A, B, C, D, E, F, G, H;
    uint32_t i1, i2, i3;
    int16_t t0, t1;

    /*  index calculation for the input as, */
    /*  pSrc[i0 + 0], pSrc[i0 + fftLen/4], pSrc[i0 + fftLen/2], pSrc[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pSrc[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pSrc[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pSrc[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pSrc[i2 * 2U];
    /* H0 = (yb-yd), H1 = (xb-xd) */
    H = __SUB2(B, D);
    /* G0 = (yb+yd), G1 = (xb+xd) */
    G = __ADD2(B, D);
    /* E0 = (ya+yc), E1 = (xa+xc) */
    E = __ADD2(A, C);
    /* F0 = (ya-yc), F1 = (xa-xc) */
    F = __SUB2(A, C);
    H = __SRA2(H, ((v2s){ 1, 1 }));
    G = __SRA2(G, ((v2s){ 1, 1 }));
    E = __SRA2(E, ((v2s){ 1, 1 }));
    t0 = (int16_t) H[0];
    t1 = (int16_t) H[1];
    F = __SRA2(F, ((v2s){ 1, 1 }));
    /* xa' = (xa+xb+xc+xd) */
    /* ya' = (ya+yb+yc+yd) */
    *((v2s *)&pSrc[i0 * 2U]) = __ADD2(E, G);
    /* A0 = (xb-xd), A1 = (yd-yb) */
    A = __PACK2(t1, -t0);
    /* B0 = (xd-xb), B1 = (yb-yd) */
    B = __PACK2(-t1, t0);
    /* xc' = (xa-xb+xc-xd) */
    /* yc' = (ya-yb+yc-yd) */
    E = __SUB2(E, G);
    /* xb' = (xa+yb-xc-yd) */
    /* yb' = (ya-xb-yc+xd) */
    A = __ADD2(F, A);
    /* xd' = (xa-yb-xc+yd) */
    /* yd' = (ya+xb-yc-xd) */
    B = __ADD2(F, B);
    *((v2s *)&pSrc[i1 * 2U]) = E;
    *((v2s *)&pSrc[i2 * 2U]) = A;
    *((v2s *)&pSrc[i3 * 2U]) = B;
}

#endif
