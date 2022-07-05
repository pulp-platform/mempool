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

        bank_id = core_id / n2_store;
        wing_id = core_id % n2_store;
        offset = bank_id * n2;
        for(j = wing_id * 4; j < MIN(wing_id * 4 + 4, n2); j++) {
          CoSi1 = *(v2s *)&pCoef_src[2U * (j               + offset)];
          CoSi2 = *(v2s *)&pCoef_src[2U * (j + 1 * N_BANKS + offset)];
          CoSi3 = *(v2s *)&pCoef_src[2U * (j + 2 * N_BANKS + offset)];
          if(i0 % 4 == 0) {
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
          for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
            radix4p_butterfly(  pSrc + idx_row * (N_BANKS * 8), pDst + idx_row * (N_BANKS * 8),
                                CoSi1, CoSi2, CoSi3, offset + j, n2, n2_store);
          }
        }

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
        radix4p_butterfly_last(pSrc + idx_row * (N_BANKS * 8), pDst + idx_row * (N_BANKS * 8), i0, col_id, fftLen);
      }
    }
    pTmp = pSrc;
    pSrc = pDst;
    pDst = pTmp;

    /* BITREVERSAL */
    if(bitReverseFlag) {
      mempool_log_partial_barrier(2, absolute_core_id, nPE);
      pSrc = pSrc + col_id * fftLen;
      for (j = 2 * core_id; j < bitReverseLen; j += 2 * nPE) {
        v2s addr, tmpa, tmpb;
        addr = __SRA2(*(v2s *)&pBitRevTable[j], ((v2s){ 2, 2 }));
        for(int32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
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

    v2s A, B, C, D, E, F, G, H;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s C1, C2, C3;
    C1 = __PACK2(-CoSi1[1], CoSi1[0]);
    C2 = __PACK2(-CoSi2[1], CoSi2[0]);
    C3 = __PACK2(-CoSi3[1], CoSi3[0]);

    /* index calculation for the input as, */
    /* pSrc16[i0 + 0], pSrc16[i0 + fftLen/4], pSrc16[i0 + fftLen/2], pSrc16[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;

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
    *((v2s *)&pDst[i0_store * 2U]) = A;
    *((v2s *)&pDst[i1_store * 2U]) = E;
    *((v2s *)&pDst[i2_store * 2U]) = F;
    *((v2s *)&pDst[i3_store * 2U]) = G;
}

static inline void radix4p_butterfly( int16_t* pSrc,
                        int16_t* pDst,
                        v2s CoSi1,
                        v2s CoSi2,
                        v2s CoSi3,
                        uint32_t i0,
                        uint32_t n2,
                        uint32_t n2_store) {

    v2s A, B, C, D, E, F, G, H;
    int16_t t0, t1, t2, t3, t4, t5;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s C1, C2, C3;
    C1 = __PACK2(-CoSi1[1], CoSi1[0]);
    C2 = __PACK2(-CoSi2[1], CoSi2[0]);
    C3 = __PACK2(-CoSi3[1], CoSi3[0]);

    /*  index calculation for the input as, */
    /*  pSrc16[i0 + 0], pSrc16[i0 + fftLen/4], pSrc16[i0 + fftLen/2], pSrc16[i0 +
     * 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = (i0 % n2_store) + (i0 / n2) * n2 + ( (i0 % n2) / n2_store) * N_BANKS;
    i1_store = i0_store + n2_store;
    i2_store = i1_store + n2_store;
    i3_store = i2_store + n2_store;

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
    *((v2s *)&pDst[i0_store * 2U]) = __SRA2(D, ((v2s){ 1, 1 }));
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
    *((v2s *)&pDst[i1_store * 2U]) = A;
    *((v2s *)&pDst[i2_store * 2U]) = B;
    *((v2s *)&pDst[i3_store * 2U]) = C;
}

static inline void radix4p_butterfly_last(  int16_t* pSrc,
                              int16_t* pDst,
                              uint32_t i0) {

    v2s A, B, C, D, E, F, G, H;
    int16_t t0, t1;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;

    /*  index calculation for the input as, */
    /*  pSrc16[i0 + 0], pSrc16[i0 + fftLen/4],
        pSrc16[i0 + fftLen/2], pSrc16[i0 + 3fftLen/4] */
    i1 = i0 + N_BANKS;
    i2 = i1 + N_BANKS;
    i3 = i2 + N_BANKS;
    i0_store = i0 * 4 + col_id * fftLen;
    i1_store = i0_store + 1;
    i2_store = i1_store + 1;
    i3_store = i2_store + 1;
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
    *((v2s *)&pDst[i0_store * 2U]) = __ADD2(E, G);
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
    *((v2s *)&pDst[i1_store * 2U]) = E;
    *((v2s *)&pDst[i2_store * 2U]) = A;
    *((v2s *)&pDst[i3_store * 2U]) = B;

}
