#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#define __HAL_RISCV_BUILTINS_V2_H__
#include "xpulp/builtins_v2.h"
#include "define.h"

static void mempool_radix2_cfft_q16p(   uint16_t fftLen,
                                        int16_t *pTwiddle,
                                        uint16_t *pBitRevTable,
                                        int16_t *pSrc,
                                        uint16_t bitReverseLen,
                                        uint8_t ifftFlag,
                                        uint8_t bitReverseFlag,
                                        uint32_t nPE);

static void mempool_radix2_butterfly_q16p(  int16_t *pSrc16,
                                            uint32_t fftLen,
                                            int16_t *pCoef16,
                                            uint32_t twidCoefModifier,
                                            uint32_t nPE);

void mempool_radix2_bitreversal_q16p(  uint16_t *pSrc,
                                      const uint16_t bitRevLen,
                                      const uint16_t *pBitRevTab,
                                      uint32_t nPE);

void mempool_radix2_cfft_q16p(  uint16_t fftLen,
                                int16_t *pTwiddle,
                                uint16_t *pBitRevTable,
                                int16_t *pSrc,
                                uint16_t bitReverseLen,
                                uint8_t ifftFlag,
                                uint8_t bitReverseFlag,
                                uint32_t nPE) {
    if (ifftFlag == 0) {
      mempool_radix2_butterfly_q16p(pSrc, fftLen, pTwiddle, 1U, nPE);
    }

    if (bitReverseFlag) {
      mempool_radix2_bitreversal_q16p((uint16_t *)pSrc, bitReverseLen, pBitRevTable, nPE);
    }
}

static void mempool_radix2_butterfly_q16p(  int16_t *pSrc16,
                                            uint32_t fftLen,
                                            int16_t *pCoef16,
                                            uint32_t twidCoefModifier,
                                            uint32_t nPE) {

  uint32_t i, j, k, l;
  uint32_t n1, n2, ia;
  uint32_t core_id = mempool_get_core_id();
  uint32_t step, steps, butt_id, offset;
  v2s T, S, R;
  v2s coeff;
  int16_t out1, out2;

  n1 = fftLen;
  n2 = n1 >> 1;
  step = (n2 + nPE - 1)/nPE;

  // loop for groups
  for (i = core_id*step; i < MIN(core_id*step + step, n2); i++) {

    coeff = *(v2s *)&pCoef16[i * 2U];

    /* Reading i and i+fftLen/2 inputs */
    /* Input is downscaled by 1 to avoid overflow */
    l = i + n2;
    /* Read ya (real), xa (imag) input */
    T = __SRA2(*(v2s *)&pSrc16[i * 2U], ((v2s){ 1, 1 }));
    /* Read yb (real), xb (imag) input */
    S = __SRA2(*(v2s *)&pSrc16[l * 2U], ((v2s){ 1, 1 }));

    /* R0 = (ya - yb) */
    /* R1 = (xa - xb) */
    R = __SUB2(T, S);

    /*  writing the butterfly processed i sample */
    /* ya' = ya + yb */
    /* xa' = xa + xb */
    *((v2s *)&pSrc16[i * 2U]) = __SRA2( __ADD2(T,S), ((v2s){ 1, 1 }) );

    /* out1 = (ya - yb)*cos + (xa - xb)*sin */
    /* out2 = (ya - yb)*cos - (xa - xb)*sin */
    out1 = (int16_t)(__DOTP2(R, coeff) >> 16U);
    out2 = (int16_t)(__DOTP2(R, __PACK2(coeff[0], -coeff[1])) >> 16U);
    *((v2s *)&pSrc16[l * 2U]) = __PACK2(out2,out1);

  } /* groups loop end */

//if(core_id==0) {
//  for(uint32_t i=0; i<N_RSAMPLES; i+=2) {
//    printf("{%6d;%6d } \n", pSrc16[i], pSrc16[i+1]);
//  }
//  printf("Done PARALLEL!\n");
//}

  mempool_barrier(nPE);

  twidCoefModifier = twidCoefModifier << 1U;
  /* loop for stage */
  for (k = fftLen / 2; k > 2; k = k >> 1) {

    n1 = n2;
    n2 = n2 >> 1;

    step = (n2+nPE-1)/nPE;
    butt_id = core_id%n2;
    offset = (core_id/n2)*n1;
    ia = butt_id*step;

    /* loop for groups */
    for (j = butt_id*step; j < MIN(butt_id*step+step,n2); j++) {
    //for (j = core_id * step; j < MIN(core_id*step + step, n2); j++) {

      coeff = *(v2s *)&pCoef16[ia * 2U];
      ia = ia + twidCoefModifier;

      /* loop for butterfly */
      for (i = offset + j; i < fftLen; i += ((nPE/n2) + 1)*n1)
      //for (i = j; i < fftLen; i += n1)
      {

        /* Reading i and i+fftLen/2 inputs */
        /* Input is downscaled by 1 to avoid overflow */
        l = i + n2;
        /* Read ya (real), xa (imag) input */
        T = __SRA2(*(v2s *)&pSrc16[i * 2U], ((v2s){ 1, 1 }));
        /* Read yb (real), xb (imag) input */
        S = __SRA2(*(v2s *)&pSrc16[l * 2U], ((v2s){ 1, 1 }));
        /* R0 = (ya - yb) */
        /* R1 = (xa - xb) */
        R = __SUB2(T, S);
        /*  writing the butterfly processed i sample */
        /* ya' = ya + yb */
        /* xa' = xa + xb */
        *((v2s *)&pSrc16[i * 2U]) = __SRA2( __ADD2(T,S), ((v2s){ 1, 1 }) );
        /* out1 = (ya - yb)*cos + (xa - xb)*sin */
        /* out2 = (ya - yb)*cos - (xa - xb)*sin */
        out1 = (int16_t)(__DOTP2(R, coeff) >> 16U);
        out2 = (int16_t)(__DOTP2(R, __PACK2(coeff[0], -coeff[1])) >> 16U);
        *((v2s *)&pSrc16[l * 2U]) = __PACK2(out2,out1);

      } /* butterfly loop end */

    } /* groups loop end */

    twidCoefModifier = twidCoefModifier << 1U;
    mempool_barrier(nPE);
  } /* stages loop end */

//if(core_id==0) {
//  for(uint32_t i=0; i<N_RSAMPLES; i+=2) {
//    printf("{%6d;%6d } \n", pSrc16[i], pSrc16[i+1]);
//  }
//  printf("Done PARALLEL!\n");
//}
//mempool_barrier(nPE);

  n1 = n2;
  n2 = n2 >> 1;
  steps = fftLen/n1;
  step = (steps + nPE - 1)/nPE;
  /* loop for butterfly */

  for (i = core_id * step * n1; i < MIN((core_id * step + step) * n1, fftLen); i += n1) {

    l = i + n2;
    /* Read ya (real), xa (imag) input */
    T = __SRA2(*(v2s *)&pSrc16[i * 2U], ((v2s){ 1, 1 }));
    /* Read yb (real), xb (imag) input */
    S = __SRA2(*(v2s *)&pSrc16[l * 2U], ((v2s){ 1, 1 }));
    /* R0 = (ya - yb) */
    /* R1 = (xa - xb) */
    R = __SUB2(T, S);
    /* ya' = ya + yb */
    /* xa' = xa + xb */
    *((v2s *)&pSrc16[i * 2U]) = __ADD2(T, S);
    /* yb' = ya - yb */
    /* xb' = xa - xb */
    *((v2s *)&pSrc16[l * 2U]) = R;

  } /* groups loop end */


//if(core_id==0) {
//  for(uint32_t i=0; i<N_RSAMPLES; i+=2) {
//    printf("{%6d;%6d } \n", pSrc16[i], pSrc16[i+1]);
//  }
//  printf("Done PARALLEL!\n");
//}

  mempool_barrier(nPE);

}

void mempool_radix2_bitreversal_q16p( uint16_t *pSrc,
                                      const uint16_t bitRevLen,
                                      const uint16_t *pBitRevTab,
                                      uint32_t nPE) {
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




