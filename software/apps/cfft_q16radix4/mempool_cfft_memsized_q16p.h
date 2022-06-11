// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#ifdef TWIDDLE_MODIFIER
static inline void mempool_memsized_butterfly(int16_t *pSrc16, int16_t *pDst16, uint32_t fftLen, int16_t *pCoef_src, uint32_t nPE);
#else
static inline void mempool_memsized_butterfly(int16_t *pSrc16, int16_t *pDst16, uint32_t fftLen, int16_t *pCoef_src, int16_t *pCoef_dst, uint32_t nPE);
#endif
static inline void fold_radix4(  int16_t *pSrc16, uint32_t fftLen, uint32_t nPE);

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
      mempool_bitreversal_q16p((uint16_t *)pSrc, bitReverseLen, pBitRevTable, nPE);
    }

}

#ifdef TWIDDLE_MODIFIER
void mempool_memsized_butterfly(  int16_t *pSrc16,
                                  int16_t *pDst16,
                                  uint32_t fftLen,
                                  int16_t *pCoef_src,
                                  uint32_t nPE)
#else
void mempool_memsized_butterfly(  int16_t *pSrc16,
                                  int16_t *pDst16,
                                  uint32_t fftLen,
                                  int16_t *pCoef_src,
                                  int16_t *pCoef_dst,
                                  uint32_t nPE)
#endif
{

    uint32_t core_id = mempool_get_core_id();
    v2s R, S, T, U, V, X, Y;
    v2s CoSi1, CoSi2, CoSi3;
    uint32_t n1, n2, ic, i0, i1, i2, i3, j, k;
    uint32_t n2_store, i0_store, i1_store, i2_store, i3_store;
    uint32_t offset, wing_id, bank_id;
    int16_t *pTmp;

    #ifdef TWIDDLE_MODIFIER
    uint32_t ic;
    uint32_t twidCoefModifier = 1U;
    #endif

    if(fftLen <= N_BANKS)
      fold_radix4(pSrc16, fftLen, nPE);

    n1 = fftLen;
    n2 = n1 >> 2U;
    n2_store = n2 >> 2U;
    for(i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {

        #ifdef TWIDDLE_MODIFIER
        CoSi1 = *(v2s *)&pCoef_src[2U * i0];
        CoSi2 = *(v2s *)&pCoef_src[2U * (i0 * 2U)];
        CoSi3 = *(v2s *)&pCoef_src[2U * (i0 * 3U)];
        #else
        CoSi1 = *(v2s *)&pCoef_src[2U * i0];
        CoSi2 = *(v2s *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
        CoSi3 = *(v2s *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
//        CoSi1 = *(v2s *)&pCoef_src[2U * i0];
//        CoSi2 = *(v2s *)&pCoef_src[2U * (i0 * 2U)];
//        CoSi3 = *(v2s *)&pCoef_src[2U * (i0 * 3U)];
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
        #endif
//        dump_ic(pCoef_src[2U * ic]);
//        dump_ic_2(pCoef_src[2U * (ic + 1 * N_BANKS)]);
//        dump_ic_3(pCoef_src[2U * (ic + 2 * N_BANKS)]);

        i1 = i0 + N_BANKS;
        i2 = i1 + N_BANKS;
        i3 = i2 + N_BANKS;
        i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ( (i0 % n2) / n2_store) * N_BANKS;
        i1_store = i0_store + n2_store;
        i2_store = i1_store + n2_store;
        i3_store = i2_store + n2_store;

        /* Read ya (real), xa(imag) input */
        X = __SRA2(*(v2s *)&pSrc16[i0 * 2U], ((v2s){ 2, 2 }));
        /* Read yc (real), xc(imag) input */
        Y = __SRA2(*(v2s *)&pSrc16[i2 * 2U], ((v2s){ 2, 2 }));
        /* Read yb (real), xb(imag) input */
        T = __SRA2(*(v2s *)&pSrc16[i1 * 2U], ((v2s){ 2, 2 }));
        /* Read yd (real), xd(imag) input */
        U = __SRA2(*(v2s *)&pSrc16[i3 * 2U], ((v2s){ 2, 2 }));
        /* R0 = (ya + yc), R1 = (xa + xc) */
        R = __ADD2(X, Y);
        /* S0 = (ya - yc), S1 =(xa - xc) */
        S = __SUB2(X, Y);
        /* T0 = (yb + yd), T1 = (xb + xd) */
        V = __ADD2(T, U);

        /*  writing the butterfly processed i0 sample */
        /* xa' = xa + xb + xc + xd, ya' = ya + yb + yc + yd */
        *((v2s *)&pDst16[i0_store * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));

        /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
        R = __SUB2(R, V);

        /*  writing the butterfly processed i0 + fftLen/4 sample */
        /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2), yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
        *((v2s *)&pDst16[i1_store * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi2, R) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi2[1], CoSi2[0]), R) >> 16U));

        /* T0 = yb-yd, T1 = xb-xd */
        T = __SUB2(T, U);
        /* R0 = (ya-yc) + (xb- xd), R1 = (xa-xc) - (yb-yd)) */
        R = __ADD2(S, __PACK2(-T[1], T[0]));
        /* S0 = (ya-yc) - (xb- xd), S1 = (xa-xc) + (yb-yd)) */
        S = __ADD2(S, __PACK2(T[1], -T[0]));

        /*  Butterfly process for the i0+fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1), yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
        *((v2s *)&pDst16[i2_store * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));
        /*  Butterfly process for the i0+3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3), yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
        *((v2s *)&pDst16[i3_store * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));

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
    // mempool_log_barrier(2, core_id);
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
                ic = j*twidCoefModifier;
                CoSi1 = *(v2s *)&pCoef_src[ic * 2U];
                CoSi2 = *(v2s *)&pCoef_src[2U * (ic * 2U)];
                CoSi3 = *(v2s *)&pCoef_src[3U * (ic * 2U)];
                #else
                CoSi1 = *(v2s *)&pCoef_src[2U * (i0               + offset)];
                CoSi2 = *(v2s *)&pCoef_src[2U * (i0 + 1 * N_BANKS + offset)];
                CoSi3 = *(v2s *)&pCoef_src[2U * (i0 + 2 * N_BANKS + offset)];
                if(i0 % 4 == 0) {
                    ic = i0 / 4 + offset;
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
//                    dump_ic((offset + n2_store     +               i0 / 4));
//                    dump_ic_2((offset + n2_store     + 1 * N_BANKS + i0 / 4));
//                    dump_ic_3((offset + n2_store     + 2 * N_BANKS + i0 / 4));
                }
                #endif
//                dump_ic(i0);
//                dump_ic_2(i0 * 2U);
//                dump_ic_3(i0 * 3U);
//                dump_ic(pCoef_src[2U * (i0               + offset)]);
//                dump_ic_2(pCoef_src[2U * (i0 + 1 * N_BANKS + offset)]);
//                dump_ic_3(pCoef_src[2U * (i0 + 2 * N_BANKS + offset)]);

                i0 = offset + j;
                // for (i0 = offset + j; i0 < fftLen; i0 += fftLen) {
                i1 = i0 + N_BANKS;
                i2 = i1 + N_BANKS;
                i3 = i2 + N_BANKS;

                i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ( (i0 % n2) / n2_store) * N_BANKS;
                i1_store = i0_store + n2_store;
                i2_store = i1_store + n2_store;
                i3_store = i2_store + n2_store;
                /* Read ya (real), xa(imag) input */
                X = *(v2s *)&pSrc16[i0 * 2U];
                /* Read yc (real), xc(imag) input */
                Y = *(v2s *)&pSrc16[i2 * 2U];
                /* Read yb (real), xb(imag) input */
                T = *(v2s *)&pSrc16[i1 * 2U];
                /* Read yd (real), xd(imag) input */
                U = *(v2s *)&pSrc16[i3 * 2U];
                /* R0 = (ya + yc), R1 = (xa + xc) */
                R = __ADD2(X, Y);
                /* S0 = (ya - yc), S1 =(xa - xc) */
                S = __SUB2(X, Y);
                /* T0 = (yb + yd), T1 = (xb + xd) */
                V = __ADD2(T, U);
                /*  writing the butterfly processed i0 sample */
                /* xa' = xa + xb + xc + xd */
                /* ya' = ya + yb + yc + yd */
                *((v2s *)&pDst16[i0_store * 2U]) =
                    __SRA2(__ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 }))),
                           ((v2s){ 1, 1 }));
                /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
                R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));
                /* Writing the butterfly processed i0 + fftLen/4 sample */
                /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
                /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
                *((v2s *)&pDst16[i1_store * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi2, R) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi2[1], CoSi2[0]), R) >> 16U));
                /* T0 = yb-yd, T1 = xb-xd */
                T = __SRA2(__SUB2(T, U), ((v2s){ 1, 1 }));
                /* R0 = (ya-yc) + (xb- xd), R1 = (xa-xc) - (yb-yd)) */
                R = __ADD2(__SRA2(S, ((v2s){ 1, 1 })), __PACK2(-T[1], T[0]));
                /* S0 = (ya-yc) - (xb- xd), S1 = (xa-xc) + (yb-yd)) */
                S = __ADD2(__SRA2(S, ((v2s){ 1, 1 })), __PACK2(T[1], -T[0]));
                /*  Butterfly process for the i0+fftLen/2 sample */
                /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
                /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
                *((v2s *)&pDst16[i2_store * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));
                /* Butterfly process for the i0+3fftLen/4 sample */
                /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
                /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
                *((v2s *)&pDst16[i3_store * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));
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

      // mempool_log_barrier(2, core_id);
      mempool_log_partial_barrier(2, core_id, n2);
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /*  Initializations for the last stage */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {

        i1 = i0 + N_BANKS;
        i2 = i1 + N_BANKS;
        i3 = i2 + N_BANKS;
        i0_store = i0 * 4;
        i1_store = i0_store + 1;
        i2_store = i1_store + 1;
        i3_store = i2_store + 1;

        /* Read ya (real), xa(imag) input */
        X = *(v2s *)&pSrc16[i0 * 2U];
        /* Read yc (real), xc(imag) input */
        Y = *(v2s *)&pSrc16[i2 * 2U];
        /* Read yb (real), xb(imag) input */
        T = *(v2s *)&pSrc16[i1 * 2U];
        /* Read yd (real), xd(imag) input */
        U = *(v2s *)&pSrc16[i3 * 2U];

        /* R0 = (ya + yc), R1 = (xa + xc) */
        R = __ADD2(X, Y);
        /* S0 = (ya - yc), S1 = (xa - xc) */
        S = __SUB2(X, Y);
        /* T0 = (yb + yd), T1 = (xb + xd)) */
        V = __ADD2(T, U);

        /* Writing the butterfly processed i0 sample */
        /* xa' = xa + xb + xc + xd, ya' = ya + yb + yc + yd */
        *((v2s *)&pDst16[i0_store * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));

        /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
        R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(T, ((v2s){ 1, 1 })));

        /* Writing the butterfly processed i0 + fftLen/4 sample */
        /* xc' = (xa-xb+xc-xd), yc' = (ya-yb+yc-yd) */
        *((v2s *)&pDst16[i1_store * 2U]) = R;

        /* T0 = (yb - yd), T1 = (xb - xd)  */
        T = __SUB2(T, U);
        T = __SRA2(T, ((v2s){ 1, 1 }));
        S = __SRA2(S, ((v2s){ 1, 1 }));

        /* Writing the butterfly processed i0 + fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd), yb' = (ya-xb-yc+xd) */
        *((v2s *)&pDst16[i2_store * 2U]) = __ADD2(S, __PACK2(T[1], -T[0]));

        /* Writing the butterfly processed i0 + 3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd), yd' = (ya+xb-yc-xd) */
        *((v2s *)&pDst16[i3_store * 2U]) = __ADD2(S, __PACK2(-T[1], T[0]));

    }

    pTmp = pSrc16;
    pSrc16 = pDst16;
    pDst16 = pTmp;

    mempool_log_partial_barrier(2, core_id, nPE);
    /* END OF LAST STAGE PROCESSING */

}

void fold_radix4 (  int16_t *pSrc16,
                    uint32_t fftLen,
                    uint32_t nPE) {

    uint32_t n2, i0, i1, i2, i3;
    uint32_t i1_store, i2_store, i3_store;
    uint32_t core_id = mempool_get_core_id();
    n2 = fftLen >> 2U;
    for(i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;
        i1_store = i0 + N_BANKS;
        i2_store = i1_store + N_BANKS;
        i3_store = i2_store + N_BANKS;
        pSrc16[i1_store * 2U] = pSrc16[i1 * 2U];
        pSrc16[i2_store * 2U] = pSrc16[i2 * 2U];
        pSrc16[i3_store * 2U] = pSrc16[i3 * 2U];
    }
    // mempool_log_barrier(2, core_id);
    mempool_log_partial_barrier(2, core_id, nPE);
}
