// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

static void mempool_cfft_q16p(  int16_t *pSrc,
                                int16_t *pDst,
                                uint32_t fftLen,
                                int16_t *pCoef_src,
                                int16_t *pCoef_dst,
                                uint16_t *pBitRevTable,
                                uint16_t bitReverseLen,
                                uint8_t bitReverseFlag,
                                uint32_t nPE);

static inline void radix4p_butterfly_first( int16_t* pSrc,
                                            int16_t* pDst,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            uint32_t i0,
                                            uint32_t n2,
                                            uint32_t n2_store);

static inline void radix4p_butterfly( int16_t* pSrc,
                                      int16_t* pDst,
                                      v2s CoSi1,
                                      v2s CoSi2,
                                      v2s CoSi3,
                                      uint32_t i0,
                                      uint32_t n2,
                                      uint32_t n2_store);

static inline void radix4p_butterfly_last(  int16_t* pSrc,
                                            int16_t* pDst,
                                            uint32_t i0);


static void mempool_cfft_columnwrapper( int16_t *pSrc,
                                        int16_t *pDst,
                                        uint32_t fftLen,
                                        int16_t *pCoef_src,
                                        int16_t *pCoef_dst,
                                        uint16_t *pBitRevTable,
                                        uint16_t bitReverseLen,
                                        uint8_t bitReverseFlag,
                                        uint32_t nPE) {

  uint32_t col_fftLen = fftLen >> 2U;
  uint32_t core_id = mempool_get_core_id();
  uint32_t col_id = core_id / (fftLen >> 4U);
  for(uint32_t idx_col = col_id; idx_col < N_FFTs_COL; idx_col += N_FFTs_COL) {
    mempool_cfft_q16p(  pSrc + col_id * col_fftLen,
                        pDst + col_id * col_fftLen,
                        fftLen,
                        pCoef_src + col_id * col_fftLen,
                        pCoef_dst + col_id * col_fftLen,
                        pBitRevTable,
                        bitReverseLen,
                        bitReverseFlag,
                        nPE);
  }
  //mempool_log_barrier(2, core_id);
  mempool_log_partial_barrier(2, core_id, nPE);

}

static void mempool_cfft_q16p(  int16_t *pSrc,
                                int16_t *pDst,
                                uint32_t fftLen,
                                int16_t *pCoef_src,
                                int16_t *pCoef_dst,
                                uint16_t *pBitRevTable,
                                uint16_t bitReverseLen,
                                uint8_t bitReverseFlag,
                                uint32_t nPE)
{
    uint32_t absolute_core_id = mempool_get_core_id();
    uint32_t core_id = absolute_core_id % (fftLen >> 4U);

    uint32_t n1, n2, i0, ic, j, k;
    uint32_t n2_store;
    uint32_t offset, wing_id, bank_id;
    int16_t *pTmp;
    v2s CoSi1, CoSi2, CoSi3;

    /* FIRST STAGE */
    n1 = fftLen;
    n2 = n1 >> 2U;
    n2_store = n2 >> 2U;
    for(i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
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
      for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        radix4p_butterfly_first(  pSrc + idx_row * (N_BANKS * 8), pDst + idx_row * (N_BANKS * 8),
                                  CoSi1, CoSi2, CoSi3,
                                  i0, n2, n2_store);
      }
    }
    pTmp = pSrc;
    pSrc = pDst;
    pDst = pTmp;
    pTmp = pCoef_src;
    pCoef_src = pCoef_dst;
    pCoef_dst = pTmp;
    mempool_log_partial_barrier(2, absolute_core_id, nPE);

    /* MIDDLE STAGE */
    for (k = fftLen / 4U; k > 4U; k >>= 2U) {

      n1 = n2;
      n2 >>= 2U;
      n2_store = n2 >> 2U;
      //if(absolute_core_id < nFFTs_COL * (fftLen >> 4U)) {

        bank_id = core_id / n2_store;
        wing_id = core_id % n2_store;
        offset = bank_id * n2;
        for(j = wing_id * 4; j < MIN(wing_id * 4 + 4, n2); j++) {
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
          }
          for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
            radix4p_butterfly(  pSrc + idx_row * (N_BANKS * 8), pDst + idx_row * (N_BANKS * 8),
                                CoSi1, CoSi2, CoSi3, offset + j, n2, n2_store);
          }
        }

      //}
      pTmp = pSrc;
      pSrc = pDst;
      pDst = pTmp;
      pTmp = pCoef_src;
      pCoef_src = pCoef_dst;
      pCoef_dst = pTmp;
      mempool_log_partial_barrier(2, absolute_core_id, n2);
    }

    /*  LAST STAGE */
    n1 = n2;
    n2 >>= 2U;
    for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {
      for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        radix4p_butterfly_last(pSrc + idx_row * (N_BANKS * 8), pDst + idx_row * (N_BANKS * 8), i0);
      }
    }
    pTmp = pSrc;
    pSrc = pDst;
    pDst = pTmp;

    /* BITREVERSAL */
    if(bitReverseFlag) {
      mempool_log_partial_barrier(2, absolute_core_id, nPE);
      for (i0 = 4*core_id; i0 < bitReverseLen; i0 += N_BANKS) {
        for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
          v2s addr, tmpa, tmpb;

          addr = __SRA2(*(v2s *)&pBitRevTable[i0], ((v2s){ 2, 2 }));
          tmpa = *(v2s *)&pSrc[addr[0] + idx_row * (N_BANKS * 8)];
          tmpb = *(v2s *)&pSrc[addr[1] + idx_row * (N_BANKS * 8)];
          *((v2s *)&pSrc[addr[0] + idx_row * (N_BANKS * 8)]) = tmpb;
          *((v2s *)&pSrc[addr[1] + idx_row * (N_BANKS * 8)]) = tmpa;

          addr = __SRA2(*(v2s *)&pBitRevTable[i0 + 2], ((v2s){ 2, 2 }));
          tmpa = *(v2s *)&pSrc[addr[0] + idx_row * (N_BANKS * 8)];
          tmpb = *(v2s *)&pSrc[addr[1] + idx_row * (N_BANKS * 8)];
          *((v2s *)&pSrc[addr[0] + idx_row * (N_BANKS * 8)]) = tmpb;
          *((v2s *)&pSrc[addr[1] + idx_row * (N_BANKS * 8)]) = tmpa;

        }
      }
    }

}

static inline void radix4p_butterfly_first( int16_t* pSrc,
                                            int16_t* pDst,
                                            v2s CoSi1,
                                            v2s CoSi2,
                                            v2s CoSi3,
                                            uint32_t i0,
                                            uint32_t n2,
                                            uint32_t n2_store) {

    v2s R, S, T, U, V, X, Y;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;

    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ( (i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;

    /* Read ya (real), xa(imag) input */
    X = __SRA2(*(v2s *)&pSrc[i0 * 2U], ((v2s){ 2, 2 }));
    /* Read yc (real), xc(imag) input */
    Y = __SRA2(*(v2s *)&pSrc[i2 * 2U], ((v2s){ 2, 2 }));
    /* Read yb (real), xb(imag) input */
    T = __SRA2(*(v2s *)&pSrc[i1 * 2U], ((v2s){ 2, 2 }));
    /* Read yd (real), xd(imag) input */
    U = __SRA2(*(v2s *)&pSrc[i3 * 2U], ((v2s){ 2, 2 }));
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R = __ADD2(X, Y);
    /* S0 = (ya - yc), S1 =(xa - xc) */
    S = __SUB2(X, Y);
    /* T0 = (yb + yd), T1 = (xb + xd) */
    V = __ADD2(T, U);

    /*  writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd, ya' = ya + yb + yc + yd */
    *((v2s *)&pDst[i0_store * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));

    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R = __SUB2(R, V);

    /*  writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2), yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    *((v2s *)&pDst[i1_store * 2U]) =
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
    *((v2s *)&pDst[i2_store * 2U]) =
        __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));
    /*  Butterfly process for the i0+3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3), yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    *((v2s *)&pDst[i3_store * 2U]) =
        __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));
}

static inline void radix4p_butterfly( int16_t* pSrc,
                        int16_t* pDst,
                        v2s CoSi1,
                        v2s CoSi2,
                        v2s CoSi3,
                        uint32_t i0,
                        uint32_t n2,
                        uint32_t n2_store) {

    v2s R, S, T, U, V, X, Y;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;

    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ( (i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;
    /* Read ya (real), xa(imag) input */
    X = *(v2s *)&pSrc[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    Y = *(v2s *)&pSrc[i2 * 2U];
    /* Read yb (real), xb(imag) input */
    T = *(v2s *)&pSrc[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    U = *(v2s *)&pSrc[i3 * 2U];
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R = __ADD2(X, Y);
    /* S0 = (ya - yc), S1 =(xa - xc) */
    S = __SUB2(X, Y);
    /* T0 = (yb + yd), T1 = (xb + xd) */
    V = __ADD2(T, U);
    /*  writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd */
    /* ya' = ya + yb + yc + yd */
    *((v2s *)&pDst[i0_store * 2U]) =
        __SRA2(__ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 }))),
               ((v2s){ 1, 1 }));
    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));
    /* Writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    *((v2s *)&pDst[i1_store * 2U]) =
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
    *((v2s *)&pDst[i2_store * 2U]) =
        __PACK2((int16_t)(__DOTP2(CoSi1, S) >> 16U),
                (int16_t)(__DOTP2(__PACK2(-CoSi1[1], CoSi1[0]), S) >> 16U));
    /* Butterfly process for the i0+3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    *((v2s *)&pDst[i3_store * 2U]) =
        __PACK2((int16_t)(__DOTP2(CoSi3, R) >> 16U),
                (int16_t)(__DOTP2(__PACK2(-CoSi3[1], CoSi3[0]), R) >> 16U));
}

static inline void radix4p_butterfly_last(  int16_t* pSrc,
                              int16_t* pDst,
                              uint32_t i0) {

    v2s R, S, T, U, V, X, Y;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;

    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = i0 * 4;
    i1_store = i0_store + 1;
    i2_store = i1_store + 1;
    i3_store = i2_store + 1;

    /* Read ya (real), xa(imag) input */
    X = *(v2s *)&pSrc[i0 * 2U];
    /* Read yc (real), xc(imag) input */
    Y = *(v2s *)&pSrc[i2 * 2U];
    /* Read yb (real), xb(imag) input */
    T = *(v2s *)&pSrc[i1 * 2U];
    /* Read yd (real), xd(imag) input */
    U = *(v2s *)&pSrc[i3 * 2U];
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R = __ADD2(X, Y);
    /* S0 = (ya - yc), S1 = (xa - xc) */
    S = __SUB2(X, Y);
    /* T0 = (yb + yd), T1 = (xb + xd)) */
    V = __ADD2(T, U);

    /* Writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd, ya' = ya + yb + yc + yd */
    *((v2s *)&pDst[i0_store * 2U]) = __ADD2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(V, ((v2s){ 1, 1 })));
    
    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R = __SUB2(__SRA2(R, ((v2s){ 1, 1 })), __SRA2(T, ((v2s){ 1, 1 })));
    /* Writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd), yc' = (ya-yb+yc-yd) */
    *((v2s *)&pDst[i1_store * 2U]) = R;

    /* T0 = (yb - yd), T1 = (xb - xd)  */
    T = __SUB2(T, U);
    T = __SRA2(T, ((v2s){ 1, 1 }));
    S = __SRA2(S, ((v2s){ 1, 1 }));

    /* Writing the butterfly processed i0 + fftLen/2 sample */
    /* xb' = (xa+yb-xc-yd), yb' = (ya-xb-yc+xd) */
    *((v2s *)&pDst[i2_store * 2U]) = __ADD2(S, __PACK2(T[1], -T[0]));
    /* Writing the butterfly processed i0 + 3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd), yd' = (ya+xb-yc-xd) */
    *((v2s *)&pDst[i3_store * 2U]) = __ADD2(S, __PACK2(-T[1], T[0]));
}
