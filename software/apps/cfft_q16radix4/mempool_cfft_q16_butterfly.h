// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifndef MEMSIZED

static void mempool_radix4_butterfly_q16s_riscv32(  int16_t *pSrc16,
                                                    uint32_t fftLen,
                                                    int16_t *pCoef16,
                                                    uint32_t twidCoefModifier);

static void mempool_radix4_butterfly_q16s_xpulpimg( int16_t *pSrc16,
                                                    uint32_t fftLen,
                                                    int16_t *pCoef16,
                                                    uint32_t twidCoefModifier);

static void mempool_radix4_butterfly_q16p_xpulpimg( int16_t *pSrc16,
                                                    uint32_t fftLen,
                                                    const int16_t *pCoef16,
                                                    uint32_t twidCoefModifier,
                                                    uint32_t nPE);

static inline void radix4_butterfly_first(  int16_t* pIn,
                                            uint32_t i0,
                                            uint32_t n2,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3);

static inline void radix4_butterfly_middle( int16_t* pIn,
                                            uint32_t i0,
                                            uint32_t n2,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3);

static inline void radix4_butterfly_last(   int16_t* pIn,
                                            uint32_t i0,
                                            uint32_t n2);


static void mempool_radix4_butterfly_q16s_riscv32(  int16_t* pIn,
                                                    uint32_t fftLen,
                                                    int16_t* pCoef16,
                                                    uint32_t twidCoefModifier) {

    int16_t R0, R1, S0, S1, T0, T1, U0, U1;
    int16_t Co1, Si1, Co2, Si2, Co3, Si3, out1, out2;
    uint32_t n1, n2, ic, i0, i1, i2, i3, j, k;

    /* START OF FIRST STAGE PROCESS */
    n2 = fftLen;
    n1 = n2;
    n2 >>= 2U;
    ic = 0U;
    for (i0 = 0; i0 < n2; i0++) {

        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;

        /* Reading i0, i0+fftLen/2 inputs */
        /* input is down scale by 4 to avoid overflow */
        /* Read ya (real), xa (imag) input */
        T0 = pSrc16[i0 * 2U] >> 2U;
        T1 = pSrc16[(i0 * 2U) + 1U] >> 2U;
        /* input is down scale by 4 to avoid overflow */
        /* Read yc (real), xc(imag) input */
        S0 = pSrc16[i2 * 2U] >> 2U;
        S1 = pSrc16[(i2 * 2U) + 1U] >> 2U;
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
        T0 = pSrc16[i1 * 2U] >> 2U;
        T1 = pSrc16[(i1 * 2U) + 1U] >> 2U;
        /* input is down scale by 4 to avoid overflow */
        /* Read yd (real), xd(imag) input */
        U0 = pSrc16[i3 * 2U] >> 2U;
        U1 = pSrc16[(i3 * 2U) + 1U] >> 2U;
        /* T0 = (yb + yd) */
        T0 = (int16_t) __CLIP(T0 + U0, 15);
        /* T1 = (xb + xd) */
        T1 = (int16_t) __CLIP(T1 + U1, 15);
        /*  writing the butterfly processed i0 sample */
        /* ya' = ya + yb + yc + yd */
        /* xa' = xa + xb + xc + xd */
        pSrc16[i0 * 2] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
        pSrc16[(i0 * 2) + 1] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
        /* R0 = (ya + yc) - (yb + yd) */
        /* R1 = (xa + xc) - (xb + xd) */
        R0 = (int16_t) __CLIP(R0 - T0, 15);
        R1 = (int16_t) __CLIP(R1 - T1, 15);
        /* co2 & si2 are read from Coefficient pointer */
        Co2 = pCoef16[2U * ic * 2U];
        Si2 = pCoef16[(2U * ic * 2U) + 1];
        /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
        out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
        /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
        out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
        /*  Reading i0+fftLen/4 */
        /* input is down scale by 4 to avoid overflow */
        /* T0 = yb, T1 =  xb */
        T0 = pSrc16[i1 * 2U] >> 2;
        T1 = pSrc16[(i1 * 2U) + 1] >> 2;
        /* writing the butterfly processed i0 + fftLen/4 sample */
        /* writing output(xc', yc') in little endian format */
        pSrc16[i1 * 2U] = out1;
        pSrc16[(i1 * 2U) + 1] = out2;
        /*  Butterfly calculations */
        /* input is down scale by 4 to avoid overflow */
        /* U0 = yd, U1 = xd */
        U0 = pSrc16[i3 * 2U] >> 2;
        U1 = pSrc16[(i3 * 2U) + 1] >> 2;
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
        /* co1 & si1 are read from Coefficient pointer */
        Co1 = pCoef16[ic * 2U];
        Si1 = pCoef16[(ic * 2U) + 1];
        /*  Butterfly process for the i0+fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
        out1 = (int16_t)((Si1 * S1 + Co1 * S0) >> 16);
        /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
        out2 = (int16_t)((-Si1 * S0 + Co1 * S1) >> 16);
        /* writing output(xb', yb') in little endian format */
        pSrc16[i2 * 2U] = out1;
        pSrc16[(i2 * 2U) + 1] = out2;
        /* Co3 & si3 are read from Coefficient pointer */
        Co3 = pCoef16[3U * (ic * 2U)];
        Si3 = pCoef16[(3U * (ic * 2U)) + 1];
        /*  Butterfly process for the i0+3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
        out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
        /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
        out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
        /* writing output(xd', yd') in little endian format */
        pSrc16[i3 * 2U] = out1;
        pSrc16[(i3 * 2U) + 1] = out2;

        /*  Twiddle coefficients index modifier */
        ic = ic + twidCoefModifier;

    };
    /* END OF FIRST STAGE PROCESS */

    /* START OF MIDDLE STAGE PROCESS */
    twidCoefModifier <<= 2U;
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {

        /*  Initializations for the middle stage */
        n1 = n2;
        n2 >>= 2U;
        ic = 0U;
        for (j = 0U; j <= (n2 - 1U); j++) {

            /*  index calculation for the coefficients */
            Co1 = pCoef16[ic * 2U];
            Si1 = pCoef16[(ic * 2U) + 1U];
            Co2 = pCoef16[2U * (ic * 2U)];
            Si2 = pCoef16[(2U * (ic * 2U)) + 1U];
            Co3 = pCoef16[3U * (ic * 2U)];
            Si3 = pCoef16[(3U * (ic * 2U)) + 1U];
            /*  Twiddle coefficients index modifier */
            ic = ic + twidCoefModifier;

            /*  Butterfly implementation */
            for (i0 = j; i0 < fftLen; i0 += n1) {

                i1 = i0 + n2;
                i2 = i1 + n2;
                i3 = i2 + n2;

                /*  Reading i0, i0+fftLen/2 inputs */
                /* Read ya (real), xa(imag) input */
                T0 = pSrc16[i0 * 2U];
                T1 = pSrc16[(i0 * 2U) + 1U];
                /* Read yc (real), xc(imag) input */
                S0 = pSrc16[i2 * 2U];
                S1 = pSrc16[(i2 * 2U) + 1U];
                /* R0 = (ya + yc), R1 = (xa + xc) */
                R0 = (int16_t) __CLIP(T0 + S0, 15);
                R1 = (int16_t) __CLIP(T1 + S1, 15);
                /* S0 = (ya - yc), S1 =(xa - xc) */
                S0 = (int16_t) __CLIP(T0 - S0, 15);
                S1 = (int16_t) __CLIP(T1 - S1, 15);
                /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
                /* Read yb (real), xb(imag) input */
                T0 = pSrc16[i1 * 2U];
                T1 = pSrc16[(i1 * 2U) + 1U];
                /* Read yd (real), xd(imag) input */
                U0 = pSrc16[i3 * 2U];
                U1 = pSrc16[(i3 * 2U) + 1U];
                /* T0 = (yb + yd), T1 = (xb + xd) */
                T0 = (int16_t) __CLIP(T0 + U0, 15);
                T1 = (int16_t) __CLIP(T1 + U1, 15);
                /*  writing the butterfly processed i0 sample */
                /* xa' = xa + xb + xc + xd */
                /* ya' = ya + yb + yc + yd */
                out1 = (int16_t)(((R0 >> 1U) + (T0 >> 1U)) >> 1U);
                out2 = (int16_t)(((R1 >> 1U) + (T1 >> 1U)) >> 1U);
                pSrc16[i0 * 2U] = out1;
                pSrc16[(2U * i0) + 1U] = out2;
                /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
                R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
                R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
                /* (ya-yb+yc-yd)* (si2) + (xa-xb+xc-xd)* co2 */
                out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
                /* (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
                out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
                /*  Reading i0+3fftLen/4 */
                /* Read yb (real), xb(imag) input */
                T0 = pSrc16[i1 * 2U];
                T1 = pSrc16[(i1 * 2U) + 1U];
                /*  writing the butterfly processed i0 + fftLen/4 sample */
                /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
                /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
                pSrc16[i1 * 2U] = out1;
                pSrc16[(i1 * 2U) + 1U] = out2;
                /*  Butterfly calculations */
                /* Read yd (real), xd(imag) input */
                U0 = pSrc16[i3 * 2U];
                U1 = pSrc16[(i3 * 2U) + 1U];
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
                pSrc16[i2 * 2U] = out1;
                pSrc16[(i2 * 2U) + 1U] = out2;
                /*  Butterfly process for the i0+3fftLen/4 sample */
                out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
                out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
                /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
                /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
                pSrc16[i3 * 2U] = out1;
                pSrc16[(i3 * 2U) + 1U] = out2;
            }
        }
        /*  Twiddle coefficients index modifier */
        twidCoefModifier <<= 2U;
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /* START OF LAST STAGE PROCESSING */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = 0U; i0 < fftLen; i0 += n1) {

        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;

        /*  Reading i0, i0+fftLen/2 inputs */
        /* Read ya (real), xa(imag) input */
        T0 = pSrc16[i0 * 2U];
        T1 = pSrc16[(i0 * 2U) + 1U];
        /* Read yc (real), xc(imag) input */
        S0 = pSrc16[i2 * 2U];
        S1 = pSrc16[(i2 * 2U) + 1U];
        /* R0 = (ya + yc), R1 = (xa + xc) */
        R0 = (int16_t) __CLIP(T0 + S0, 15);
        R1 = (int16_t) __CLIP(T1 + S1, 15);
        /* S0 = (ya - yc), S1 = (xa - xc) */
        S0 = (int16_t) __CLIP(T0 - S0, 15);
        S1 = (int16_t) __CLIP(T1 - S1, 15);
        /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
        /* Read yb (real), xb(imag) input */
        T0 = pSrc16[i1 * 2U];
        T1 = pSrc16[(i1 * 2U) + 1U];
        /* Read yd (real), xd(imag) input */
        U0 = pSrc16[i3 * 2U];
        U1 = pSrc16[(i3 * 2U) + 1U];
        /* T0 = (yb + yd), T1 = (xb + xd)) */
        T0 = (int16_t) __CLIP(T0 + U0, 15);
        T1 = (int16_t) __CLIP(T1 + U1, 15);
        /*  writing the butterfly processed i0 sample */
        /* xa' = xa + xb + xc + xd */
        /* ya' = ya + yb + yc + yd */
        pSrc16[i0 * 2U] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
        pSrc16[(i0 * 2U) + 1U] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
        /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
        R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
        R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
        /* Read yb (real), xb(imag) input */
        T0 = pSrc16[i1 * 2U];
        T1 = pSrc16[(i1 * 2U) + 1U];
        /*  writing the butterfly processed i0 + fftLen/4 sample */
        /* xc' = (xa-xb+xc-xd) */
        /* yc' = (ya-yb+yc-yd) */
        pSrc16[i1 * 2U] = R0;
        pSrc16[(i1 * 2U) + 1U] = R1;
        /* Read yd (real), xd(imag) input */
        U0 = pSrc16[i3 * 2U];
        U1 = pSrc16[(i3 * 2U) + 1U];
        /* T0 = (yb - yd), T1 = (xb - xd)  */
        T0 = (int16_t) __CLIP(T0 - U0, 15);
        T1 = (int16_t) __CLIP(T1 - U1, 15);
        /*  writing the butterfly processed i0 + fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd) */
        /* yb' = (ya-xb-yc+xd) */
        pSrc16[i2 * 2U] = (int16_t)((S0 >> 1U) + (T1 >> 1U));
        pSrc16[(i2 * 2U) + 1U] = (int16_t)((S1 >> 1U) - (T0 >> 1U));
        /*  writing the butterfly processed i0 + 3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd) */
        /* yd' = (ya+xb-yc-xd) */
        pSrc16[i3 * 2U] = (int16_t)((S0 >> 1U) - (T1 >> 1U));
        pSrc16[(i3 * 2U) + 1U] = (int16_t)((S1 >> 1U) + (T0 >> 1U));

    }
    /* END OF LAST STAGE PROCESSING */
}

static void mempool_radix4_butterfly_q16s_xpulpimg(   int16_t *pSrc16,
                                                      uint32_t fftLen,
                                                      int16_t *pCoef16,
                                                      uint32_t twidCoefModifier) {

    v2s CoSi1, CoSi2, CoSi3;
    v2s C1, C2, C3;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t n1, n2, ic, i0, j, k;

    n2 = fftLen;
    n1 = n2;
    n2 >>= 2U;
    ic = 0U;

    /* START OF FIRST STAGE PROCESS */
    for(i0 = 0; i0 < n2; i0++) {
        CoSi1 = *(v2s *)&pCoef16[ic * 2U];
        CoSi2 = *(v2s *)&pCoef16[2U * ic * 2U];
        CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
        #ifndef ASM
        t1 = (int16_t) CoSi1[1];
        t3 = (int16_t) CoSi2[1];
        t5 = (int16_t) CoSi3[1];
        t0 = (int16_t) CoSi1[0];
        t2 = (int16_t) CoSi2[0];
        t4 = (int16_t) CoSi3[0];
        C1 = __PACK2(-t1, t0);
        C2 = __PACK2(-t3, t2);
        C3 = __PACK2(-t5, t4);
        #else
        asm volatile(
            "pv.extract.h  %[t1],%[CoSi1],1;"
            "pv.extract.h  %[t3],%[CoSi2],1;"
            "pv.extract.h  %[t5],%[CoSi3],1;"
            "pv.extract.h  %[t0],%[CoSi1],0;"
            "pv.extract.h  %[t2],%[CoSi2],0;"
            "pv.extract.h  %[t4],%[CoSi3],0;"
            "sub           %[t1],zero,%[t1];"
            "sub           %[t3],zero,%[t3];"
            "sub           %[t5],zero,%[t5];"
            "pv.pack.h %[C1],%[t1],%[t0];"
            "pv.pack.h %[C2],%[t3],%[t2];"
            "pv.pack.h %[C3],%[t5],%[t4];"
            : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
              [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
              [t4] "=&r" (t4), [t5] "=&r" (t5)
            : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
            : );
        #endif
        radix4_butterfly_first(  pSrc16, i0, n2,
                                  CoSi1, CoSi2, CoSi3,
                                  C1, C2, C3);
        ic = ic + twidCoefModifier;
    }
    /* END OF FIRST STAGE PROCESS */

    /* START OF MIDDLE STAGE PROCESS */
    twidCoefModifier <<= 2U;
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {
        n1 = n2;
        n2 >>= 2U;
        ic = 0U;
        for (j = 0U; j <= (n2 - 1U); j++) {
            /*  index calculation for the coefficients */
            CoSi1 = *(v2s *)&pCoef16[ic * 2U];
            CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
            CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
            #ifndef ASM
            t1 = (int16_t) CoSi1[1];
            t3 = (int16_t) CoSi2[1];
            t5 = (int16_t) CoSi3[1];
            t0 = (int16_t) CoSi1[0];
            t2 = (int16_t) CoSi2[0];
            t4 = (int16_t) CoSi3[0];
            C1 = __PACK2(-t1, t0);
            C2 = __PACK2(-t3, t2);
            C3 = __PACK2(-t5, t4);
            #else
            asm volatile(
            "pv.extract.h  %[t1],%[CoSi1],1;"
            "pv.extract.h  %[t3],%[CoSi2],1;"
            "pv.extract.h  %[t5],%[CoSi3],1;"
            "pv.extract.h  %[t0],%[CoSi1],0;"
            "pv.extract.h  %[t2],%[CoSi2],0;"
            "pv.extract.h  %[t4],%[CoSi3],0;"
            "sub           %[t1],zero,%[t1];"
            "sub           %[t3],zero,%[t3];"
            "sub           %[t5],zero,%[t5];"
            "pv.pack.h %[C1],%[t1],%[t0];"
            "pv.pack.h %[C2],%[t3],%[t2];"
            "pv.pack.h %[C3],%[t5],%[t4];"
            : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
              [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
              [t4] "=&r" (t4), [t5] "=&r" (t5)
            : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
            : );
            #endif
            /*  Twiddle coefficients index modifier */
            ic = ic + twidCoefModifier;
            /*  Butterfly implementation */
            for (i0 = j; i0 < fftLen; i0 += n1) {
              radix4_butterfly_middle( pSrc16, i0, n2,
                                        CoSi1, CoSi2, CoSi3,
                                        C1, C2, C3);
            }
        }
        twidCoefModifier <<= 2U;
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /* START OF LAST STAGE PROCESSING */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = 0U; i0 < fftLen; i0 += n1) {
      radix4_butterfly_last(pSrc16, i0, n2);
    }
    /* END OF LAST STAGE PROCESSING */
}

static void mempool_radix4_butterfly_q16p_xpulpimg( int16_t *pSrc16,
                                    uint32_t fftLen,
                                    const int16_t *pCoef16,
                                    uint32_t twidCoefModifier,
                                    uint32_t nPE) {

    v2s CoSi1, CoSi2, CoSi3;
    v2s C1, C2, C3;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t n1, n2, ic, i0, j, k;
    uint32_t absolute_core_id = mempool_get_core_id();
    uint32_t core_id = absolute_core_id%nPE;
    uint32_t step, steps;

    /* START OF FIRST STAGE PROCESS */
    n1 = fftLen;
    n2 = n1 >> 2U;
    step = (n2 + nPE - 1) / nPE;
    for (i0 = core_id * step; i0 < MIN(core_id * step + step, n2); i0++) {

        /*  Twiddle coefficients index modifier */
        ic = i0 * twidCoefModifier;
        /* co1 & si1 are read from Coefficient pointer */
        CoSi1 = *(v2s *)&pCoef16[ic * 2U];
        /* co2 & si2 are read from Coefficient pointer */
        CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
        /* co3 & si3 are read from Coefficient pointer */
        CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
        #ifndef ASM
        t1 = (int16_t) CoSi1[1];
        t3 = (int16_t) CoSi2[1];
        t5 = (int16_t) CoSi3[1];
        t0 = (int16_t) CoSi1[0];
        t2 = (int16_t) CoSi2[0];
        t4 = (int16_t) CoSi3[0];
        C1 = __PACK2(-t1, t0);
        C2 = __PACK2(-t3, t2);
        C3 = __PACK2(-t5, t4);
        #else
        asm volatile(
        "pv.extract.h  %[t1],%[CoSi1],1;"
        "pv.extract.h  %[t3],%[CoSi2],1;"
        "pv.extract.h  %[t5],%[CoSi3],1;"
        "pv.extract.h  %[t0],%[CoSi1],0;"
        "pv.extract.h  %[t2],%[CoSi2],0;"
        "pv.extract.h  %[t4],%[CoSi3],0;"
        "sub           %[t1],zero,%[t1];"
        "sub           %[t3],zero,%[t3];"
        "sub           %[t5],zero,%[t5];"
        "pv.pack.h %[C1],%[t1],%[t0];"
        "pv.pack.h %[C2],%[t3],%[t2];"
        "pv.pack.h %[C3],%[t5],%[t4];"
        : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
          [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
          [t4] "=&r" (t4), [t5] "=&r" (t5)
        : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
        : );
        #endif
        radix4_butterfly_first( pSrc16, i0, n2,
                                CoSi1, CoSi2, CoSi3,
                                C1, C2, C3);
    }
    mempool_log_barrier(2, absolute_core_id);
    /* END OF FIRST STAGE PROCESS */

    /* START OF MIDDLE STAGE PROCESS */
    twidCoefModifier <<= 2U;
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {

        uint32_t offset, butt_id;
        n1 = n2;
        n2 >>= 2U;
        step = (n2 + nPE - 1) / nPE;
        butt_id = core_id % n2;
        offset = (core_id / n2) * n1;
        for(j = butt_id * step; j < MIN(butt_id * step + step, n2); j++) {
            /*  Twiddle coefficients index modifier */
            ic = twidCoefModifier * j;
            CoSi1 = *(v2s *)&pCoef16[ic * 2U];
            CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
            CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
            #ifndef ASM
            t1 = (int16_t) CoSi1[1];
            t3 = (int16_t) CoSi2[1];
            t5 = (int16_t) CoSi3[1];
            t0 = (int16_t) CoSi1[0];
            t2 = (int16_t) CoSi2[0];
            t4 = (int16_t) CoSi3[0];
            C1 = __PACK2(-t1, t0);
            C2 = __PACK2(-t3, t2);
            C3 = __PACK2(-t5, t4);
            #else
            asm volatile(
            "pv.extract.h  %[t1],%[CoSi1],1;"
            "pv.extract.h  %[t3],%[CoSi2],1;"
            "pv.extract.h  %[t5],%[CoSi3],1;"
            "pv.extract.h  %[t0],%[CoSi1],0;"
            "pv.extract.h  %[t2],%[CoSi2],0;"
            "pv.extract.h  %[t4],%[CoSi3],0;"
            "sub           %[t1],zero,%[t1];"
            "sub           %[t3],zero,%[t3];"
            "sub           %[t5],zero,%[t5];"
            "pv.pack.h %[C1],%[t1],%[t0];"
            "pv.pack.h %[C2],%[t3],%[t2];"
            "pv.pack.h %[C3],%[t5],%[t4];"
            : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
              [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
              [t4] "=&r" (t4), [t5] "=&r" (t5)
            : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
            : );
            #endif
            /*  Butterfly implementation */
            for (i0 = offset + j; i0 < fftLen; i0 += ((nPE + n2 - 1) / n2) * n1) {
              radix4_butterfly_middle( pSrc16, i0, n2,
                                        CoSi1, CoSi2, CoSi3,
                                        C1, C2, C3);
            }
        }
        twidCoefModifier <<= 2U;
        mempool_log_barrier(2, absolute_core_id);
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /* START OF LAST STAGE PROCESSING */
    n1 = n2;
    n2 >>= 2U;
    steps = fftLen / n1;
    step = (steps + nPE - 1) / nPE;
    /*  Butterfly implementation */
    for (i0 = core_id * step * n1; i0 < MIN((core_id * step + step) * n1, fftLen); i0 += n1) {
      radix4_butterfly_last(pSrc16, i0, n2);
    }
    mempool_log_barrier(2, absolute_core_id);
    /* END OF LAST STAGE PROCESSING */
}

/**
  @brief         Last butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/

static inline void radix4_butterfly_first( int16_t* pIn,
                                            uint32_t i0,
                                            uint32_t n2,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3) {
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    v2s A, B, C, D, E, F, G, H;

    /* index calculation for the input as, */
    /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;

    #ifndef ASM
    v2s s1 = {1, 1};
    v2s s2 = {2, 2};
    /* Read yb (real), xb(imag) input */
    B = __SRA2(*(v2s *)&pIn[i1 * 2U], s2);
    /* Read yd (real), xd(imag) input */
    D = __SRA2(*(v2s *)&pIn[i3 * 2U], s2);
    /* Read ya (real), xa (imag) input */
    A = __SRA2(*(v2s *)&pIn[i0 * 2U], s2);
    /* Read yc (real), xc(imag) input */
    C = __SRA2(*(v2s *)&pIn[i2 * 2U], s2);
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
    A = __SRA2(E, s1);
    B = __SRA2(G, s1);
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
    *((v2s *)&pIn[i0 * 2U]) = A;
    *((v2s *)&pIn[i1 * 2U]) = E;
    *((v2s *)&pIn[i2 * 2U]) = F;
    *((v2s *)&pIn[i3 * 2U]) = G;
    #else
    v2s s1, s2;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa (imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    asm volatile (
    "addi %[s1], zero, 1;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 1;"
    "addi %[s2], zero, 2;"
    "slli %[s2], %[s2], 0x10;"
    "addi %[s2], %[s2], 2;"
    "pv.sra.h  %[B],%[B],%[s2];"
    "pv.sra.h  %[D],%[D],%[s2];"
    "pv.sra.h  %[A],%[A],%[s2];"
    "pv.sra.h  %[C],%[C],%[s2];"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sra.h  %[A],%[E],%[s1];"
    "pv.sra.h  %[B],%[G],%[s1];"
    "sub %[t3],zero,%[t1];"
    "pv.pack.h %[C],%[t3],%[t0];"
    "sub %[t4],zero,%[t0];"
    "pv.pack.h %[D],%[t1],%[t4];"
    "pv.sub.h  %[E],%[E],%[G];"
    "pv.add.h  %[G],%[F],%[C];"
    "pv.add.h  %[H],%[F],%[D];"
    "pv.dotsp.h  %[C],%[CoSi2],%[E];"
    "pv.dotsp.h  %[D],%[C2],%[E];"
    "pv.dotsp.h  %[E],%[CoSi1],%[H];"
    "pv.dotsp.h  %[F],%[C1],%[H];"
    "srai  %[t0],%[C],0x10;"
    "srai  %[t1],%[D],0x10;"
    "pv.dotsp.h  %[C],%[CoSi3],%[G];"
    "pv.dotsp.h  %[D],%[C3],%[G];"
    "srai  %[t2],%[E],0x10;"
    "srai  %[t3],%[F],0x10;"
    "srai  %[t4],%[C],0x10;"
    "srai  %[t5],%[D],0x10;"
    "pv.add.h  %[A],%[A],%[B];"
    "pv.pack.h %[E],%[t0],%[t1];"
    "pv.pack.h %[F],%[t2],%[t3];"
    "pv.pack.h %[G],%[t4],%[t5];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
      [t4] "=&r" (t4), [t5] "=&r" (t5), [s1] "=&r" (s1), [s2] "=&r" (s2),
      [C1] "+r" (C1), [C2] "+r" (C2), [C3] "+r" (C3) :
      [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
    : );
    *((v2s *)&pIn[i0 * 2U]) = A;
    *((v2s *)&pIn[i1 * 2U]) = E;
    *((v2s *)&pIn[i2 * 2U]) = F;
    *((v2s *)&pIn[i3 * 2U]) = G;
    #endif
}

/**
  @brief         Last butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/

static inline void radix4_butterfly_middle(  int16_t* pIn,
                                              uint32_t i0,
                                              uint32_t n2,
                                              v2s CoSi1,
                                              v2s CoSi2,
                                              v2s CoSi3,
                                              v2s C1,
                                              v2s C2,
                                              v2s C3) {
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    v2s A, B, C, D, E, F, G, H;
    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
     * 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;

    #ifndef ASM
    v2s s1 = {1, 1};
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* G0 = (yb + yd), G1 = (xb + xd) */
    G = __ADD2(B, D);
    /* H0 = (yb - yd), H1 = (xb - xd) */
    H = __SUB2(B, D);
    /* E0 = (ya + yc), E1 = (xa + xc) */
    E = __ADD2(A, C);
    /* F0 = (ya - yc), F1 =(xa - xc) */
    F = __SUB2(A, C);
    G = __SRA2(G, s1);
    H = __SRA2(H, s1);
    E = __SRA2(E, s1);
    F = __SRA2(F, s1);
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
    *((v2s *)&pIn[i0 * 2U]) = __SRA2(D, s1);
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
    *((v2s *)&pIn[i1 * 2U]) = A;
    *((v2s *)&pIn[i2 * 2U]) = B;
    *((v2s *)&pIn[i3 * 2U]) = C;
    #else
    v2s s1;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    asm volatile (
    "pv.add.h  %[G],%[B],%[D];"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.sra.h  %[G],%[G],%[s1];"
    "pv.sra.h  %[H],%[H],%[s1];"
    "pv.sra.h  %[E],%[E],%[s1];"
    "pv.sra.h  %[F],%[F],%[s1];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sub.h  %[C],%[E],%[G];"
    "pv.add.h  %[D],%[E],%[G];"
    "sub %[t3],zero,%[t0];"
    "pv.pack.h %[A],%[t1],%[t3];"
    "sub %[t4],zero,%[t1];"
    "pv.pack.h %[B],%[t4],%[t0];"
    "pv.sra.h  %[D],%[D],%[s1];"
    "pv.add.h  %[E],%[F],%[A];"
    "pv.add.h  %[F],%[F],%[B];"
    "pv.dotsp.h  %[G],%[CoSi2],%[C];"
    "pv.dotsp.h  %[H],%[C2],%[C];"
    "pv.dotsp.h  %[A],%[CoSi1],%[F];"
    "pv.dotsp.h  %[B],%[C1],%[F];"
    "srai  %[t0],%[G],0x10;"
    "srai  %[t1],%[H],0x10;"
    "pv.dotsp.h  %[G],%[CoSi3],%[E];"
    "pv.dotsp.h  %[H],%[C3],%[E];"
    "srai  %[t2],%[A],0x10;"
    "srai  %[t3],%[B],0x10;"
    "srai  %[t4],%[G],0x10;"
    "srai  %[t5],%[H],0x10;"
    "pv.pack.h %[A],%[t0],%[t1];"
    "pv.pack.h %[B],%[t2],%[t3];"
    "pv.pack.h %[C],%[t4],%[t5];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
      [t4] "=&r" (t4), [t5] "=&r" (t5), [s1] "=&r" (s1),
      [C1] "+r" (C1), [C2] "+r" (C2), [C3] "+r" (C3) :
      [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
    : );
    *((v2s *)&pIn[i0 * 2U]) = D;
    *((v2s *)&pIn[i1 * 2U]) = A;
    *((v2s *)&pIn[i2 * 2U]) = B;
    *((v2s *)&pIn[i3 * 2U]) = C;
    #endif
}

/**
  @brief         Last butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @return        none
*/

static inline void radix4_butterfly_last(   int16_t* pIn,
                                            uint32_t i0,
                                            uint32_t n2) {
    int16_t t0, t1;
    uint32_t i1, i2, i3;
    v2s A, B, C, D, E, F, G, H;

    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
        pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    #ifndef ASM
    v2s s1 = {1, 1};
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* H0 = (yb-yd), H1 = (xb-xd) */
    H = __SUB2(B, D);
    /* G0 = (yb+yd), G1 = (xb+xd) */
    G = __ADD2(B, D);
    /* E0 = (ya+yc), E1 = (xa+xc) */
    E = __ADD2(A, C);
    /* F0 = (ya-yc), F1 = (xa-xc) */
    F = __SUB2(A, C);
    H = __SRA2(H, s1);
    G = __SRA2(G, s1);
    E = __SRA2(E, s1);
    t0 = (int16_t) H[0];
    t1 = (int16_t) H[1];
    F = __SRA2(F, s1);
    /* xa' = (xa+xb+xc+xd) */
    /* ya' = (ya+yb+yc+yd) */
    *((v2s *)&pIn[i0 * 2U]) = __ADD2(E, G);
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
    *((v2s *)&pIn[i1 * 2U]) = E;
    *((v2s *)&pIn[i2 * 2U]) = A;
    *((v2s *)&pIn[i3 * 2U]) = B;
    #else
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    int16_t t2, t3;
    v2s s1;
    asm volatile (
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "addi %[s1], zero, 1;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 1;"
    "pv.sra.h  %[H],%[H],%[s1];"
    "pv.sra.h  %[G],%[G],%[s1];"
    "pv.sra.h  %[E],%[E],%[s1];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sra.h  %[F],%[F],%[s1];"
    "sub %[t2], zero, %[t0];"
    "pv.pack.h %[A],%[t1],%[t2];"
    "sub %[t3],zero,%[t1];"
    "pv.pack.h %[B],%[t3],%[t0];"
    "pv.add.h  %[H],%[E],%[G];"
    "pv.sub.h  %[E],%[E],%[G];"
    "pv.add.h  %[A],%[F],%[A];"
    "pv.add.h  %[B],%[F],%[B];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3), [s1] "=&r" (s1)
    : : );
    *((v2s *)&pIn[i0 * 2U]) = H;
    *((v2s *)&pIn[i1 * 2U]) = E;
    *((v2s *)&pIn[i2 * 2U]) = A;
    *((v2s *)&pIn[i3 * 2U]) = B;
    #endif
}

#elif defined(MEMSIZED)

/**
  @brief         Folding in local memory function
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     nPE Number of PE
  @return        none
*/

static inline void fold_radix4 (  int16_t *pSrc16,
                                  uint32_t fftLen,
                                  uint32_t nPE) {
    uint32_t n2, i0, i1, i2, i3;
    uint32_t i1_store, i2_store, i3_store;
    uint32_t core_id = mempool_get_core_id();
    volatile v2s A, B, C;
    n2 = fftLen >> 2U;
    for(i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;
        A = *(v2s *)&pSrc16[i1 * 2U];
        B = *(v2s *)&pSrc16[i2 * 2U];
        C = *(v2s *)&pSrc16[i3 * 2U];
        i1_store = i0 + N_BANKS;
        i2_store = i1_store + N_BANKS;
        i3_store = i2_store + N_BANKS;
        *(v2s *)&pSrc16[i1_store * 2U] = A;
        *(v2s *)&pSrc16[i2_store * 2U] = B;
        *(v2s *)&pSrc16[i3_store * 2U] = C;
    }
    mempool_log_partial_barrier(2, core_id, nPE);
}


#ifdef TWIDDLE_MODIFIER
static inline void mempool_memsized_butterfly(  int16_t *pSrc16,
                                                int16_t *pDst16,
                                                uint32_t fftLen,
                                                int16_t *pCoef_src,
                                                uint32_t nPE);

#else
static inline void mempool_memsized_butterfly(  int16_t *pSrc16,
                                                int16_t *pDst16,
                                                uint32_t fftLen,
                                                int16_t *pCoef_src,
                                                int16_t *pCoef_dst,
                                                uint32_t nPE);

#endif

static inline void radix4_butterfly_first(  int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
                                            uint32_t n2,
                                            uint32_t n2_store,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3);

static inline void radix4_butterfly_middle( int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
                                            uint32_t n2,
                                            uint32_t n2_store,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3);

static inline void radix4_butterfly_last(   int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0);


#ifdef TWIDDLE_MODIFIER

/**
  @brief         Full FFT butterfly
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[out]    pDst16  points to output buffer of 16b data, Re and Im parts are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     pCoef_src Twiddle coefficients vector
  @param[in]     nPE Number of PE
  @return        none
*/

static void mempool_memsized_butterfly( int16_t *pSrc16,
                                        int16_t *pDst16,
                                        uint32_t fftLen,
                                        int16_t *pCoef_src,
                                        uint32_t nPE) {
#else

/**
  @brief         Full FFT butterfly
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[out]    pDst16  points to output buffer of 16b data, Re and Im parts are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     pCoef_src Twiddle coefficients vector
  @param[in]     pCoef_dst Auxiliary twiddle coefficients vector
  @param[in]     nPE Number of PE
  @return        none
*/

static void mempool_memsized_butterfly( int16_t *pSrc16,
                                        int16_t *pDst16,
                                        uint32_t fftLen,
                                        int16_t *pCoef_src,
                                        int16_t *pCoef_dst,
                                        uint32_t nPE) {
#endif
    uint32_t core_id = mempool_get_core_id();
    v2s CoSi1, CoSi2, CoSi3;
    v2s C1, C2, C3;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t n1, n2, n2_store, i0, j, k;
    uint32_t ic, offset, wing_id, bank_id;
    int16_t *pTmp;

    #ifdef TWIDDLE_MODIFIER
    uint32_t twidCoefModifier = 1U;
    #endif

    if(fftLen <= N_BANKS)
      fold_radix4(pSrc16, fftLen, nPE);

    n1 = fftLen;
    n2 = n1 >> 2U;
    n2_store = n2 >> 2U;
    for(i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
        #ifdef TWIDDLE_MODIFIER
        ic = i0 * twidCoefModifier;
        CoSi1 = *(v2s *)&pCoef_src[2U * ic];
        CoSi2 = *(v2s *)&pCoef_src[2U * (ic * 2U)];
        CoSi3 = *(v2s *)&pCoef_src[2U * (ic * 3U)];
        t0 = (int16_t) CoSi1[0];
        t1 = (int16_t) CoSi1[1];
        t2 = (int16_t) CoSi2[0];
        t3 = (int16_t) CoSi2[1];
        t4 = (int16_t) CoSi3[0];
        t5 = (int16_t) CoSi3[1];
        C1 = __PACK2(-t1, t0);
        C2 = __PACK2(-t3, t2);
        C3 = __PACK2(-t5, t4);
        #else
        CoSi1 = *(v2s *)&pCoef_src[2U * i0];
        CoSi2 = *(v2s *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
        CoSi3 = *(v2s *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
        if(i0 % 4 == 0) {
            ic = i0 / 4;
            *((v2s *)&pCoef_dst[2U * (               ic)]) = CoSi1;
            *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
            *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
            *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
            ic += N_BANKS;
            *((v2s *)&pCoef_dst[2U * (               ic)]) = CoSi2;
            *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
            *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
            *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
            ic += N_BANKS;
            *((v2s *)&pCoef_dst[2U * (               ic)]) = CoSi3;
            *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
            *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
            *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
        }
            #ifndef ASM
            t1 = (int16_t) CoSi1[1];
            t3 = (int16_t) CoSi2[1];
            t5 = (int16_t) CoSi3[1];
            t0 = (int16_t) CoSi1[0];
            t2 = (int16_t) CoSi2[0];
            t4 = (int16_t) CoSi3[0];
            C1 = __PACK2(-t1, t0);
            C2 = __PACK2(-t3, t2);
            C3 = __PACK2(-t5, t4);
            #else
            asm volatile(
            "pv.extract.h  %[t1],%[CoSi1],1;"
            "pv.extract.h  %[t3],%[CoSi2],1;"
            "pv.extract.h  %[t5],%[CoSi3],1;"
            "pv.extract.h  %[t0],%[CoSi1],0;"
            "pv.extract.h  %[t2],%[CoSi2],0;"
            "pv.extract.h  %[t4],%[CoSi3],0;"
            "sub           %[t1],zero,%[t1];"
            "sub           %[t3],zero,%[t3];"
            "sub           %[t5],zero,%[t5];"
            "pv.pack.h %[C1],%[t1],%[t0];"
            "pv.pack.h %[C2],%[t3],%[t2];"
            "pv.pack.h %[C3],%[t5],%[t4];"
            : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
              [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
              [t4] "=&r" (t4), [t5] "=&r" (t5)
            : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
            : );
            #endif
        #endif
        radix4_butterfly_first(   pSrc16, pDst16, i0, n2, n2_store,
                                  CoSi1, CoSi2, CoSi3, C1, C2, C3);
    }
    pTmp = pSrc16;
    pSrc16 = pDst16;
    pDst16 = pTmp;
    #ifdef TWIDDLE_MODIFIER
    twidCoefModifier <<= 2U;
    #else
    pTmp = pCoef_src;
    pCoef_src = pCoef_dst;
    pCoef_dst = pTmp;
    #endif
    mempool_log_partial_barrier(2, core_id, nPE);
    /* END OF FIRST STAGE PROCESSING */

    for (k = fftLen / 4U; k > 4U; k >>= 2U) {
        n1 = n2;
        n2 >>= 2U;
        n2_store = n2 >> 2U;
        if(core_id < (fftLen >> 4U)) {
            bank_id = core_id / n2_store;
            wing_id = core_id % n2_store;
            offset = bank_id * n2;
            for(j = wing_id * 4; j < MIN(wing_id * 4 + 4, n2); j++) {
                #ifdef TWIDDLE_MODIFIER
                ic = j * twidCoefModifier;
                CoSi1 = *(v2s *)&pCoef_src[ic * 2U];
                CoSi2 = *(v2s *)&pCoef_src[2U * (ic * 2U)];
                CoSi3 = *(v2s *)&pCoef_src[3U * (ic * 2U)];
                t0 = (int16_t) CoSi1[0];
                t1 = (int16_t) CoSi1[1];
                t2 = (int16_t) CoSi2[0];
                t3 = (int16_t) CoSi2[1];
                t4 = (int16_t) CoSi3[0];
                t5 = (int16_t) CoSi3[1];
                C1 = __PACK2(-t1, t0);
                C2 = __PACK2(-t3, t2);
                C3 = __PACK2(-t5, t4);
                #else
                CoSi1 = *(v2s *)&pCoef_src[2U * (j               + offset)];
                CoSi2 = *(v2s *)&pCoef_src[2U * (j + 1 * N_BANKS + offset)];
                CoSi3 = *(v2s *)&pCoef_src[2U * (j + 2 * N_BANKS + offset)];
                if(j % 4 == 0) {
                    ic = j / 4 + offset;
                    *((v2s *)&pCoef_dst[2U * (                ic)]) = CoSi1;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 1  + ic)]) = CoSi1;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 2  + ic)]) = CoSi1;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 3  + ic)]) = CoSi1;
                    ic += N_BANKS;
                    *((v2s *)&pCoef_dst[2U * (                ic)]) = CoSi2;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 1  + ic)]) = CoSi2;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 2  + ic)]) = CoSi2;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 3  + ic)]) = CoSi2;
                    ic += N_BANKS;
                    *((v2s *)&pCoef_dst[2U * (                ic)]) = CoSi3;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 1  + ic)]) = CoSi3;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 2  + ic)]) = CoSi3;
                    *((v2s *)&pCoef_dst[2U * (n2_store * 3  + ic)]) = CoSi3;
                }
                    #ifndef ASM
                    t1 = (int16_t) CoSi1[1];
                    t3 = (int16_t) CoSi2[1];
                    t5 = (int16_t) CoSi3[1];
                    t0 = (int16_t) CoSi1[0];
                    t2 = (int16_t) CoSi2[0];
                    t4 = (int16_t) CoSi3[0];
                    C1 = __PACK2(-t1, t0);
                    C2 = __PACK2(-t3, t2);
                    C3 = __PACK2(-t5, t4);
                    #else
                    asm volatile(
                    "pv.extract.h  %[t1],%[CoSi1],1;"
                    "pv.extract.h  %[t3],%[CoSi2],1;"
                    "pv.extract.h  %[t5],%[CoSi3],1;"
                    "pv.extract.h  %[t0],%[CoSi1],0;"
                    "pv.extract.h  %[t2],%[CoSi2],0;"
                    "pv.extract.h  %[t4],%[CoSi3],0;"
                    "sub           %[t1],zero,%[t1];"
                    "sub           %[t3],zero,%[t3];"
                    "sub           %[t5],zero,%[t5];"
                    "pv.pack.h %[C1],%[t1],%[t0];"
                    "pv.pack.h %[C2],%[t3],%[t2];"
                    "pv.pack.h %[C3],%[t5],%[t4];"
                    : [C1] "=r" (C1), [C2] "=r" (C2), [C3] "=r" (C3),
                      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
                      [t4] "=&r" (t4), [t5] "=&r" (t5)
                    : [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
                    : );
                    #endif
                #endif
                i0 = offset + j;
                radix4_butterfly_middle(  pSrc16, pDst16, i0, n2, n2_store,
                                          CoSi1, CoSi2, CoSi3, C1, C2, C3);
            }
        }
        pTmp = pSrc16;
        pSrc16 = pDst16;
        pDst16 = pTmp;
        #ifdef TWIDDLE_MODIFIER
        twidCoefModifier <<= 2U;
        #else
        pTmp = pCoef_src;
        pCoef_src = pCoef_dst;
        pCoef_dst = pTmp;
        #endif
        mempool_log_partial_barrier(2, core_id, n2);
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /*  Initializations for the last stage */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {
        radix4_butterfly_last(pSrc16, pDst16, i0);
    }
    pTmp = pSrc16;
    pSrc16 = pDst16;
    pDst16 = pTmp;
    mempool_log_partial_barrier(2, core_id, nPE);
    /* END OF LAST STAGE PROCESSING */
}

/**
  @brief         First butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     n2_store number of elements in the first wing of the butterfly for next stage
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/

static inline void radix4_butterfly_first(  int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
                                            uint32_t n2,
                                            uint32_t n2_store,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            v2s C1,
                                            v2s C2,
                                            v2s C3) {
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s A, B, C, D, E, F, G, H;

    #ifndef ASM
    v2s s1 = {1, 1};
    v2s s2 = {2, 2};
    /* index calculation for the input as, */
    /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;
    /* Read yb (real), xb(imag) input */
    B = __SRA2(*(v2s *)&pIn[i1 * 2U], s2);
    /* Read yd (real), xd(imag) input */
    D = __SRA2(*(v2s *)&pIn[i3 * 2U], s2);
    /* Read ya (real), xa (imag) input */
    A = __SRA2(*(v2s *)&pIn[i0 * 2U], s2);
    /* Read yc (real), xc(imag) input */
    C = __SRA2(*(v2s *)&pIn[i2 * 2U], s2);
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
    A = __SRA2(E, s1);
    B = __SRA2(G, s1);
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
    *((v2s *)&pOut[i0_store * 2U]) = A;
    *((v2s *)&pOut[i1_store * 2U]) = E;
    *((v2s *)&pOut[i2_store * 2U]) = F;
    *((v2s *)&pOut[i3_store * 2U]) = G;
    #else
    v2s s1, s2;
    /* index calculation for the input as, */
    /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    asm volatile (
    "addi %[s2], zero, 0x02;"
    "slli %[s2], %[s2], 0x10;"
    "addi %[s2], %[s2], 0x02;"
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.sra.h  %[B],%[B],%[s2];"
    "pv.sra.h  %[D],%[D],%[s2];"
    "pv.sra.h  %[A],%[A],%[s2];"
    "pv.sra.h  %[C],%[C],%[s2];"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sra.h  %[A],%[E],%[s1];"
    "pv.sra.h  %[B],%[G],%[s1];"
    "sub %[t3],zero,%[t1];"
    "pv.pack.h %[C],%[t3],%[t0];"
    "sub %[t4],zero,%[t0];"
    "pv.pack.h %[D],%[t1],%[t4];"
    "pv.sub.h  %[E],%[E],%[G];"
    "pv.add.h  %[G],%[F],%[C];"
    "pv.add.h  %[H],%[F],%[D];"
    "pv.dotsp.h  %[C],%[CoSi2],%[E];"
    "pv.dotsp.h  %[D],%[C2],%[E];"
    "pv.dotsp.h  %[E],%[CoSi1],%[H];"
    "pv.dotsp.h  %[F],%[C1],%[H];"
    "srai  %[t0],%[C],0x10;"
    "srai  %[t1],%[D],0x10;"
    "pv.dotsp.h  %[C],%[CoSi3],%[G];"
    "pv.dotsp.h  %[D],%[C3],%[G];"
    "srai  %[t2],%[E],0x10;"
    "srai  %[t3],%[F],0x10;"
    "srai  %[t4],%[C],0x10;"
    "srai  %[t5],%[D],0x10;"
    "pv.add.h  %[A],%[A],%[B];"
    "pv.pack.h %[E],%[t0],%[t1];"
    "pv.pack.h %[F],%[t2],%[t3];"
    "pv.pack.h %[G],%[t4],%[t5];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
      [t4] "=&r" (t4), [t5] "=&r" (t5), [s1] "=&r" (s1), [s2] "=&r" (s2),
      [C1] "+r" (C1), [C2] "+r" (C2), [C3] "+r" (C3) :
      [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
    : );
    i0_store = (i0 % n2_store) + (i0 / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;
    *((v2s *)&pOut[i0_store * 2U]) = A;
    *((v2s *)&pOut[i1_store * 2U]) = E;
    *((v2s *)&pOut[i2_store * 2U]) = F;
    *((v2s *)&pOut[i3_store * 2U]) = G;
    #endif
}

/**
  @brief         Middle butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     n2_store number of elements in the first wing of the butterfly for next stage
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/

static inline void radix4_butterfly_middle(   int16_t *pIn,
                                              int16_t *pOut,
                                              uint32_t i0,
                                              uint32_t n2,
                                              uint32_t n2_store,
                                              v2s CoSi1,
                                              v2s CoSi2,
                                              v2s CoSi3,
                                              v2s C1,
                                              v2s C2,
                                              v2s C3) {

    #ifndef ASM
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s A, B, C, D, E, F, G, H;
    v2s s1 = (v2s){ 1, 1 };

    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
     * 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* G0 = (yb + yd), G1 = (xb + xd) */
    G = __ADD2(B, D);
    /* H0 = (yb - yd), H1 = (xb - xd) */
    H = __SUB2(B, D);
    /* E0 = (ya + yc), E1 = (xa + xc) */
    E = __ADD2(A, C);
    /* F0 = (ya - yc), F1 =(xa - xc) */
    F = __SUB2(A, C);
    G = __SRA2(G, s1);
    H = __SRA2(H, s1);
    E = __SRA2(E, s1);
    F = __SRA2(F, s1);
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
    D = __SRA2(D, s1);
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
    *((v2s *)&pOut[i0_store * 2U]) = D;
    *((v2s *)&pOut[i1_store * 2U]) = A;
    *((v2s *)&pOut[i2_store * 2U]) = B;
    *((v2s *)&pOut[i3_store * 2U]) = C;
    #else
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s A, B, C, D, E, F, G, H;
    v2s s1;
    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
     * 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    asm volatile (
    "pv.add.h  %[G],%[B],%[D];"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.sra.h  %[G],%[G],%[s1];"
    "pv.sra.h  %[H],%[H],%[s1];"
    "pv.sra.h  %[E],%[E],%[s1];"
    "pv.sra.h  %[F],%[F],%[s1];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sub.h  %[C],%[E],%[G];"
    "pv.add.h  %[D],%[E],%[G];"
    "sub %[t3],zero,%[t0];"
    "pv.pack.h %[A],%[t1],%[t3];"
    "sub %[t4],zero,%[t1];"
    "pv.pack.h %[B],%[t4],%[t0];"
    "pv.sra.h  %[D],%[D],%[s1];"
    "pv.add.h  %[E],%[F],%[A];"
    "pv.add.h  %[F],%[F],%[B];"
    "pv.dotsp.h  %[G],%[CoSi2],%[C];"
    "pv.dotsp.h  %[H],%[C2],%[C];"
    "pv.dotsp.h  %[A],%[CoSi1],%[F];"
    "pv.dotsp.h  %[B],%[C1],%[F];"
    "srai  %[t0],%[G],0x10;"
    "srai  %[t1],%[H],0x10;"
    "pv.dotsp.h  %[G],%[CoSi3],%[E];"
    "pv.dotsp.h  %[H],%[C3],%[E];"
    "srai  %[t2],%[A],0x10;"
    "srai  %[t3],%[B],0x10;"
    "srai  %[t4],%[G],0x10;"
    "srai  %[t5],%[H],0x10;"
    "pv.pack.h %[A],%[t0],%[t1];"
    "pv.pack.h %[B],%[t2],%[t3];"
    "pv.pack.h %[C],%[t4],%[t5];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
      [t4] "=&r" (t4), [t5] "=&r" (t5), [s1] "=&r" (s1),
      [C1] "+r" (C1), [C2] "+r" (C2), [C3] "+r" (C3) :
      [CoSi1] "r" (CoSi1), [CoSi2] "r" (CoSi2), [CoSi3] "r" (CoSi3)
    : );
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;
    *((v2s *)&pOut[i0_store * 2U]) = D;
    *((v2s *)&pOut[i1_store * 2U]) = A;
    *((v2s *)&pOut[i2_store * 2U]) = B;
    *((v2s *)&pOut[i3_store * 2U]) = C;
    #endif
}


/**
  @brief         Last butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are interleaved
  @param[in]     i0 points to the first element to be processed
  @return        none
*/

static inline void radix4_butterfly_last(   int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0) {
    int16_t t0, t1;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s A, B, C, D, E, F, G, H;

    #ifndef ASM
    v2s s1 = {1, 1};
    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
        pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = i0 * 4;
    i1_store = i0_store + 1;
    i2_store = i1_store + 1;
    i3_store = i2_store + 1;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    /* H0 = (yb-yd), H1 = (xb-xd) */
    H = __SUB2(B, D);
    /* G0 = (yb+yd), G1 = (xb+xd) */
    G = __ADD2(B, D);
    /* E0 = (ya+yc), E1 = (xa+xc) */
    E = __ADD2(A, C);
    /* F0 = (ya-yc), F1 = (xa-xc) */
    F = __SUB2(A, C);
    H = __SRA2(H, s1);
    G = __SRA2(G, s1);
    E = __SRA2(E, s1);
    t0 = (int16_t) H[0];
    t1 = (int16_t) H[1];
    F = __SRA2(F, s1);
    /* xa' = (xa+xb+xc+xd) */
    /* ya' = (ya+yb+yc+yd) */
    *((v2s *)&pOut[i0_store * 2U]) = __ADD2(E, G);
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
    *((v2s *)&pOut[i1_store * 2U]) = E;
    *((v2s *)&pOut[i2_store * 2U]) = A;
    *((v2s *)&pOut[i3_store * 2U]) = B;
    #else
    /*  index calculation for the input as, */
    /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
        pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    /* Read yb (real), xb(imag) input */
    B = *(v2s *)&pIn[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    D = *(v2s *)&pIn[i3 * 2U];
    /* Read ya (real), xa(imag) input */
    A = *(v2s *)&pIn[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    C = *(v2s *)&pIn[i2 * 2U];
    int16_t t2, t3;
    v2s s1;
    asm volatile (
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.sra.h  %[H],%[H],%[s1];"
    "pv.sra.h  %[G],%[G],%[s1];"
    "pv.sra.h  %[E],%[E],%[s1];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sra.h  %[F],%[F],%[s1];"
    "sub %[t2], zero, %[t0];"
    "pv.pack.h %[A],%[t1],%[t2];"
    "sub %[t3],zero,%[t1];"
    "pv.pack.h %[B],%[t3],%[t0];"
    "pv.add.h  %[H],%[E],%[G];"
    "pv.sub.h  %[E],%[E],%[G];"
    "pv.add.h  %[A],%[F],%[A];"
    "pv.add.h  %[B],%[F],%[B];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3),
      [s1] "=&r" (s1)
    : );
    i0_store = i0 * 4;
    i1_store = i0_store + 1;
    i2_store = i1_store + 1;
    i3_store = i2_store + 1;
    *((v2s *)&pOut[i0_store * 2U]) = H;
    *((v2s *)&pOut[i1_store * 2U]) = E;
    *((v2s *)&pOut[i2_store * 2U]) = A;
    *((v2s *)&pOut[i3_store * 2U]) = B;
    #endif
}

#endif
