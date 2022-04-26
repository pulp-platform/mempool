#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define __HAL_RISCV_BUILTINS_V2_H__
#include "xpulp/builtins_v2.h"


static void mempool_cfft_q16p(  uint16_t fftLen,
                                int16_t *pTwiddle,
                                uint16_t *pBitRevTable,
                                int16_t *pSrc,
                                uint16_t bitReverseLen,
                                uint8_t ifftFlag,
                                uint8_t bitReverseFlag,
                                uint32_t nPE);

static void mempool_cfft_radix4by2_q16p( int16_t *pSrc,
                                        uint32_t fftLen,
                                        const int16_t *pCoef,
                                        uint32_t nPE);

static void mempool_radix4_butterfly_q16p( int16_t *pSrc16,
                                          uint32_t fftLen,
                                          int16_t *pCoef16,
                                          uint32_t twidCoefModifier,
                                          uint32_t nPE);

void mempool_bitreversal_16p( uint16_t *pSrc,
                              const uint16_t bitRevLen,
                              const uint16_t *pBitRevTab,
                              const uint32_t nPE);

void mempool_cfft_q16p( uint16_t fftLen,
                        int16_t *pTwiddle,
                        uint16_t *pBitRevTable,
                        int16_t *pSrc,
                        uint16_t bitReverseLen,
                        uint8_t ifftFlag,
                        uint8_t bitReverseFlag,
                        uint32_t nPE) {

    if (ifftFlag == 0) {
        switch (fftLen) {
        case 16:
        case 64:
        case 256:
        case 1024:
        case 4096:
            mempool_radix4_butterfly_q16p(pSrc, fftLen, pTwiddle, 1U, nPE);
            break;
        case 32:
        case 128:
        case 512:
        case 2048:
            mempool_cfft_radix4by2_q16p(pSrc, fftLen, pTwiddle, nPE);
            break;
        }
    }

//    if(mempool_get_core_id()==0) {
//      printf("Done\n");
//    }

    if (bitReverseFlag) {
//      if(mempool_get_core_id()==0) {
//        mempool_bitreversal_16s((uint16_t *)pSrc, bitReverseLen, pBitRevTable);
//      }
      mempool_bitreversal_16p((uint16_t *)pSrc, bitReverseLen, pBitRevTable, nPE);
    }

}

/* When the number of elements is not a power of four the first step must be a radix 2 butterfly */
void mempool_cfft_radix4by2_q16p(int16_t *pSrc, uint32_t fftLen, const int16_t *pCoef, uint32_t nPE) {

    uint32_t i;
    uint32_t n2, nC;
    v2s pa, pb;

    uint32_t l;
    v2s CoSi;
    v2s a, b, t;
    int16_t testa, testb;
    uint32_t core_id = mempool_get_core_id();

    n2 = fftLen >> 1;
    nC = (n2 + nPE - 1)/nPE;
    uint32_t offset = core_id*nC;
    for (i = offset; i < MIN(n2,offset + nC); i++) {

        CoSi = *(v2s *)&pCoef[i * 2];
        l = i + n2;
        a = __SRA2(*(v2s *)&pSrc[2 * i], ((v2s){ 1, 1 }));
        b = __SRA2(*(v2s *)&pSrc[2 * l], ((v2s){ 1, 1 }));
        t = __SUB2(a, b);
        *((v2s *)&pSrc[i * 2]) = __SRA2(__ADD2(a, b), ((v2s){ 1, 1 }));

        testa = (int16_t)(__DOTP2(t, CoSi) >> 16);
        testb = (int16_t)(__DOTP2(t, __PACK2(-CoSi[1], CoSi[0])) >> 16);
        *((v2s *)&pSrc[l * 2]) = __PACK2(testa, testb);

    }
    mempool_barrier(NUM_CORES);

//    mempool_radix4_butterfly_q16p((int16_t*) pSrc, n2, (int16_t *)pCoef, 2U, nPE);
//    mempool_radix4_butterfly_q16p((int16_t*) (pSrc + fftLen), n2, (int16_t *)pCoef, 2U, nPE);

    if (nPE > 1){
      if (core_id < nPE/2){
        // first col
        mempool_radix4_butterfly_q16p(pSrc, n2, (int16_t *)pCoef, 2U, nPE/2);
      } else {
        // second col
        mempool_radix4_butterfly_q16p(pSrc + fftLen, n2, (int16_t *)pCoef, 2U, nPE - nPE/2);
      }
    } else {
      // first col
      mempool_radix4_butterfly_q16p(pSrc, n2, (int16_t *)pCoef, 2U, nPE);
      // second col
      mempool_radix4_butterfly_q16p(pSrc + fftLen, n2, (int16_t *)pCoef, 2U, nPE);
    }

    for (i = offset; i < MIN((fftLen >> 1), offset + nC); i++) {
        pa = *(v2s *)&pSrc[4 * i];
        pb = *(v2s *)&pSrc[4 * i + 2];

        pa = __SLL2(pa, ((v2s){ 1, 1 }));
        pb = __SLL2(pb, ((v2s){ 1, 1 }));

        *((v2s *)&pSrc[4 * i]) = pa;
        *((v2s *)&pSrc[4 * i + 2]) = pb;
    }
    //mempool_barrier(NUM_CORES);
}

void mempool_radix4_butterfly_q16p( int16_t *pSrc16,
                                    uint32_t fftLen,
                                    int16_t *pCoef16,
                                    uint32_t twidCoefModifier,
                                    uint32_t nPE) {

    v2s R, S, T, U, V;
    v2s CoSi1, CoSi2, CoSi3;
    uint32_t n1, n2, ic, i0, i1, i2, i3, j, k;
    uint32_t core_id = mempool_get_core_id()%nPE;

    /* Total process is divided into three stages */
    /* process first stage, middle stages, & last stage */

    /* Initializations for the first stage */
    n2 = fftLen;
    n1 = n2;
    /* n2 = fftLen/4 */
    n2 >>= 2U;
    uint32_t step = (n2 + nPE - 1)/nPE;

    i0 = core_id*step;
    /* index calculation for the input as, */
    /* pSrc16[i0 + 0], pSrc16[i0 + fftLen/4], pSrc16[i0 + fftLen/2], pSrc16[i0 + 3fftLen/4] */
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;

    /* Input is in 1.15(q15) format */
    /* START OF FIRST STAGE PROCESS */
    while (i0 < MIN(core_id * step + step, n2)) {
        /* Butterfly implementation */
        /*  Twiddle coefficients index modifier */
        ic = i0 * twidCoefModifier;

        /* Reading i0, i0+fftLen/2 inputs */

        /* input is down scale by 4 to avoid overflow */
        /* Read ya (real), xa (imag) input */
        T = __SRA2(*(v2s *)&pSrc16[i0 * 2U], ((v2s){ 2, 2 }));

        /* input is down scale by 4 to avoid overflow */
        /* Read yc (real), xc(imag) input */
        S = __SRA2(*(v2s *)&pSrc16[i2 * 2U], ((v2s){ 2, 2 }));

        /* R0 = (ya + yc) */
        /* R1 = (xa + xc) */
        R = __ADD2(T, S);

        /* S0 = (ya - yc) */
        /* S1 = (xa - xc) */
        S = __SUB2(T, S);

        /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
        /* input is down scale by 4 to avoid overflow */
        /* Read yb (real), xb(imag) input */
        T = __SRA2(*(v2s *)&pSrc16[i1 * 2U], ((v2s){ 2, 2 }));

        /* input is down scale by 4 to avoid overflow */
        /* Read yd (real), xd(imag) input */
        U = __SRA2(*(v2s *)&pSrc16[i3 * 2U], ((v2s){ 2, 2 }));

        /* T0 = (yb + yd) */
        /* T1 = (xb + xd) */
        V = __ADD2(T, U);

        /*  writing the butterfly processed i0 sample */
        /* ya' = ya + yb + yc + yd */
        /* xa' = xa + xb + xc + xd */
        *((v2s *)&pSrc16[i0 * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));

        /* R0 = (ya + yc) - (yb + yd) */
        /* R1 = (xa + xc) - (xb + xd) */
        R = __SUB2(R, V);

        /* co2 & si2 are read from Coefficient pointer */
        CoSi2 = *(v2s *)&pCoef16[2U * ic * 2U];

        /*  Reading i0+fftLen/4 */
        /* input is down scale by 4 to avoid overflow */
        /* T0 = yb, T1 =  xb */
        // T = __SRA2(*(v2s *) &pSrc16[i1 *2U], ((v2s){2,2}));

        /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
        /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
        /* writing the butterfly processed i0 + fftLen/4 sample */
        /* writing output(xc', yc') in little endian format */
        *((v2s *)&pSrc16[i1 * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi2, R) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi2[1], CoSi2[0]), R) >> 16U));

        /*  Butterfly calculations */
        /* input is down scale by 4 to avoid overflow */
        /* U0 = yd, U1 = xd */
        U = __SRA2(*(v2s *)&pSrc16[i3 * 2U], ((v2s){ 2, 2 }));

        /* T0 = yb-yd */
        /* T1 = xb-xd */
        T = __SUB2(T, U);

        /* R1 = (ya-yc) + (xb- xd),  R0 = (xa-xc) - (yb-yd)) */
        R = __ADD2(S, __PACK2(-T[1], T[0]));

        /* S1 = (ya-yc) - (xb- xd), S0 = (xa-xc) + (yb-yd)) */
        S = __ADD2(S, (v2s)__PACK2(T[1], -T[0]));

        /* co1 & si1 are read from Coefficient pointer */
        CoSi1 = *(v2s *)&pCoef16[ic * 2U];

        /*  Butterfly process for the i0+fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
        /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
        /* writing output(xb', yb') in little endian format */
        *((v2s *)&pSrc16[i2 * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));

        /* Co3 & si3 are read from Coefficient pointer */
        CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];

        /*  Butterfly process for the i0+3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
        /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3)
           writing output(xd', yd') in little endian format */
        *((v2s *)&pSrc16[i3 * 2U]) =
            __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                    (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));
        i0++;

    }
    mempool_barrier(NUM_CORES);
    /* data is in 4.11(q11) format */
    /* END OF FIRST STAGE PROCESS */

    /* START OF MIDDLE STAGE PROCESS */
    /*  Twiddle coefficients index modifier */
    twidCoefModifier <<= 2U;
    uint32_t offset, butt_id;
    /*  Calculation of Middle stage */
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {

      n1 = n2;
      n2 >>= 2U;
      step = (n2+nPE-1)/nPE;

      butt_id = core_id%n2;
      offset = (core_id/n2)*n1;
      for(j = butt_id*step; j < MIN(butt_id*step+step,n2); j++) {
      //for(j = core_id*step; j < MIN(core_id*step+step,n2); j++) {

          /*  Twiddle coefficients index modifier */
          ic = twidCoefModifier * j;
          /*  index calculation for the coefficients */
          CoSi1 = *(v2s *)&pCoef16[ic * 2U];
          CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
          CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];

          /*  Butterfly implementation */
          for (i0 = offset + j; i0 < fftLen; i0 += ((nPE/n2) + 1)*n1) {
          //for (i0 = j; i0 < fftLen; i0 = i0 + n1) {

                 /*  Reading i0, i0+fftLen/2 inputs */
                /* Read ya (real), xa(imag) input */
                T = *(v2s *)&pSrc16[i0 * 2U];

                /* Read yc (real), xc(imag) input */
                S = *(v2s *)&pSrc16[i2 * 2U];

                /* R0 = (ya + yc), R1 = (xa + xc) */
                R = __ADD2(T, S);

                /* S0 = (ya - yc), S1 =(xa - xc) */
                S = __SUB2(T, S);

                /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
                /* Read yb (real), xb(imag) input */
                T = *(v2s *)&pSrc16[i1 * 2U];

                /* Read yd (real), xd(imag) input */
                U = *(v2s *)&pSrc16[i3 * 2U];

                /* T0 = (yb + yd), T1 = (xb + xd) */
                V = __ADD2(T, U);

                /*  writing the butterfly processed i0 sample */

                /* xa' = xa + xb + xc + xd */
                /* ya' = ya + yb + yc + yd */
                *((v2s *)&pSrc16[i0 * 2U]) =
                    __SRA2(__ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 }))),
                           ((v2s){ 1, 1 }));

                /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
                R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));

                /*  Reading i0+3fftLen/4 */
                /* Read yb (real), xb(imag) input */
                // T = *(v2s *) &pSrc16[i1 * 2U];

                /* (ya-yb+yc-yd)* (si2) + (xa-xb+xc-xd)* co2 */
                /* (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
                /*  writing the butterfly processed i0 + fftLen/4 sample */
                /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
                /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
                *((v2s *)&pSrc16[i1 * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi2, R) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi2[1], CoSi2[0]), R) >> 16U));

                /*  Butterfly calculations */

                /* Read yd (real), xd(imag) input */
                U = *(v2s *)&pSrc16[i3 * 2U];

                /* T0 = yb-yd, T1 = xb-xd */
                T = __SRA2(__SUB2(T, U), ((v2s){ 1, 1 }));

                /* R0 = (ya-yc) + (xb- xd), R1 = (xa-xc) - (yb-yd)) */
                R = __ADD2(__SRA2(S, ((v2s){ 1, 1 })), __PACK2(-T[1], T[0]));

                /* S0 = (ya-yc) - (xb- xd), S1 = (xa-xc) + (yb-yd)) */
                S = __ADD2(__SRA2(S, ((v2s){ 1, 1 })), __PACK2(T[1], -T[0]));

                /*  Butterfly process for the i0+fftLen/2 sample */
                /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
                /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
                *((v2s *)&pSrc16[i2 * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));

                /*  Butterfly process for the i0+3fftLen/4 sample */
                /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
                /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
                *((v2s *)&pSrc16[i3 * 2U]) =
                    __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                            (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));
          }
      }
//      if(core_id==0) {
//        printf("Done middle \n");
//        printf("n1 = %d, n2 = %d, step = %d, fftLen = %d, nPE = %d \n", n1, n2, step, fftLen, nPE);
//      }
      /*  Twiddle coefficients index modifier */
      twidCoefModifier <<= 2U;
      mempool_barrier(NUM_CORES);
    }
    /* END OF MIDDLE STAGE PROCESSING */

    /* data is in 10.6(q6) format for the 1024 point */
    /* data is in 8.8(q8) format for the 256 point */
    /* data is in 6.10(q10) format for the 64 point */
    /* data is in 4.12(q12) format for the 16 point */
    /*  Initializations for the last stage */
    n1 = n2;
    n2 >>= 2U;
    /* START OF LAST STAGE PROCESSING */
    uint32_t steps;
    /* start of last stage process */
    steps = fftLen/n1;
    step = (steps + nPE - 1)/nPE;
    
    /*  Butterfly implementation */
    for (i0 = core_id * step * n1; i0 < MIN((core_id * step + step) * n1, fftLen); i0 += n1) {
        /*  index calculation for the input as, */
        /*  pSrc16[i0 + 0], pSrc16[i0 + fftLen/4], pSrc16[i0 + fftLen/2], pSrc16[i0 + 3fftLen/4] */
        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;

        /*  Reading i0, i0+fftLen/2 inputs */
        /* Read ya (real), xa(imag) input */
        T = *(v2s *)&pSrc16[i0 * 2U];

        /* Read yc (real), xc(imag) input */
        S = *(v2s *)&pSrc16[i2 * 2U];

        /* R0 = (ya + yc), R1 = (xa + xc) */
        R = __ADD2(T, S);

        /* S0 = (ya - yc), S1 = (xa - xc) */
        S = __SUB2(T, S);

        /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
        /* Read yb (real), xb(imag) input */
        T = *(v2s *)&pSrc16[i1 * 2U];
        /* Read yd (real), xd(imag) input */
        U = *(v2s *)&pSrc16[i3 * 2U];

        /* T0 = (yb + yd), T1 = (xb + xd)) */
        T = __ADD2(T, U);

        /*  writing the butterfly processed i0 sample */
        /* xa' = xa + xb + xc + xd */
        /* ya' = ya + yb + yc + yd */
        *((v2s *)&pSrc16[i0 * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(T, ((v2s){ 1, 1 })));

        /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
        R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(T, ((v2s){ 1, 1 })));

        /* Read yb (real), xb(imag) input */
        T = *(v2s *)&pSrc16[i1 * 2U];

        /*  writing the butterfly processed i0 + fftLen/4 sample */
        /* xc' = (xa-xb+xc-xd) */
        /* yc' = (ya-yb+yc-yd) */
        *((v2s *)&pSrc16[i1 * 2U]) = R;

        /* Read yd (real), xd(imag) input */
        U = *(v2s *)&pSrc16[i3 * 2U];

        /* T0 = (yb - yd), T1 = (xb - xd)  */
        T = __SUB2(T, U);

        T = __SRA2(T, ((v2s){ 1, 1 }));
        S = __SRA2(S, ((v2s){ 1, 1 }));

        /*  writing the butterfly processed i0 + fftLen/2 sample */
        /* xb' = (xa+yb-xc-yd) */
        /* yb' = (ya-xb-yc+xd) */
        *((v2s *)&pSrc16[i2 * 2U]) = __ADD2(S, __PACK2(T[1], -T[0]));

        /*  writing the butterfly processed i0 + 3fftLen/4 sample */
        /* xd' = (xa-yb-xc+yd) */
        /* yd' = (ya+xb-yc-xd) */
        *((v2s *)&pSrc16[i3 * 2U]) = __ADD2(S, __PACK2(-T[1], T[0]));
    }
    mempool_barrier(NUM_CORES);

    /* END OF LAST STAGE PROCESSING */

    /* output is in 11.5(q5) format for the 1024 point */
    /* output is in 9.7(q7) format for the 256 point   */
    /* output is in 7.9(q9) format for the 64 point  */
    /* output is in 5.11(q11) format for the 16 point  */
}


void mempool_bitreversal_16p( uint16_t *pSrc,
                              const uint16_t bitRevLen,
                              const uint16_t *pBitRevTab,
                              const uint32_t nPE) {

    uint32_t i;
    uint32_t core_id = mempool_get_core_id();
    v2s addr, tmpa, tmpb;

    for (i = 2*core_id; i < bitRevLen; i += (2*nPE)){

      addr = *(v2s *)&pBitRevTab[i] >> 2;
      tmpa = *(v2s *)&pSrc[ addr[0] ];
      tmpb = *(v2s *)&pSrc[ addr[1] ];
      *((v2s *)&pSrc[ addr[0] ]) = tmpb;
      *((v2s *)&pSrc[ addr[1] ]) = tmpa;

    }
    mempool_barrier(NUM_CORES);
}
