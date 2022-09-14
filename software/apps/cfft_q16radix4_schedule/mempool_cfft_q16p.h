// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

static void mempool_cfft_q16p(  uint32_t col_id,
                                int16_t *pSrc,
                                int16_t *pDst,
                                uint32_t fftLen,
                                int16_t *pCoef_src,
                                int16_t *pCoef_dst,
                                uint16_t *pBitRevTable,
                                uint16_t bitReverseLen,
                                uint8_t bitReverseFlag,
                                uint32_t nPE);

static inline void radix4_butterfly_first(  int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
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
                                            uint32_t i0,
                                            uint32_t col_id,
                                            uint32_t fftLen);


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
    if (col_id < N_FFTs_COL) {
        mempool_cfft_q16p(  col_id,
                            pSrc + 2 * col_id * col_fftLen,
                            pDst + 2 * col_id * col_fftLen,
                            fftLen,
                            pCoef_src + 2 * col_id * col_fftLen,
                            pCoef_dst + 2 * col_id * col_fftLen,
                            pBitRevTable,
                            bitReverseLen,
                            bitReverseFlag,
                            nPE);
    }
    mempool_log_partial_barrier(2, core_id, N_FFTs_COL * (N_CSAMPLES >> 4U));
}

static void mempool_cfft_q16p(  uint32_t col_id,
                                int16_t *pSrc,
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
    int32_t t0, t1, t2, t3, t4, t5;
    v2s CoSi1, CoSi2, CoSi3;
    v2s C1, C2, C3;

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
        for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
            radix4_butterfly_first(   pSrc + idx_row * (N_BANKS * 8),
                                      pDst + idx_row * (N_BANKS * 8),
                                      i0, n2_store,
                                      CoSi1, CoSi2, CoSi3,
                                      C1, C2, C3);
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
            for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
                radix4_butterfly_middle(  pSrc + idx_row * (N_BANKS * 8),
                                          pDst + idx_row * (N_BANKS * 8),
                                          offset + j, n2, n2_store,
                                          CoSi1, CoSi2, CoSi3,
                                          C1, C2, C3);
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
            radix4_butterfly_last(  pSrc + idx_row * (N_BANKS * 8),
                                    pDst + idx_row * (N_BANKS * 8),
                                    i0, col_id, fftLen);
        }
    }
    pTmp = pSrc - 2 * col_id * (fftLen >> 2U);
    pSrc = pDst - 2 * col_id * (fftLen >> 2U);
    pDst = pTmp;

    /* BITREVERSAL */
    if(bitReverseFlag) {
        mempool_log_partial_barrier(2, absolute_core_id, nPE);
        #if BITREVERSE_TABLE
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
        #else
        uint16_t* ptr1 = (uint16_t*)(pSrc + col_id * fftLen);
        uint16_t* ptr2 = (uint16_t*)(pDst + col_id * fftLen);
        uint32_t addr, n;
        core_id = absolute_core_id % (fftLen >> 2U);
        for (j = core_id; j < (core_id + 4); j++) {
            n = j + fftLen;
            addr = 0;
            while (n > 0) {
                if (addr != 0)
                  addr = addr << 1;
                if ((n & 1) == 1)
                  addr = addr ^ 1;
                n = n >> 1U;
            }
            addr = (addr >> 1);
            for(uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
                *((uint32_t*)&ptr2[2 * addr + idx_row * (N_BANKS * 8)]) =
                                (uint32_t) ptr1[2 * j + idx_row * (N_BANKS * 8)];
            }
        }
        pSrc = pDst;
        #endif
    }
}

static inline void radix4_butterfly_first(  int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
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
    int16_t t0, t1, t2, t3;
    uint32_t i1, i2, i3;
    uint32_t i0_store, i1_store, i2_store, i3_store;
    v2s A, B, C, D, E, F, G, H;
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
    "sub %[t2],zero,%[t1];"
    "pv.pack.h %[C],%[t2],%[t0];"
    "sub %[t3],zero,%[t0];"
    "pv.pack.h %[D],%[t1],%[t3];"
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
    "srai  %[C],%[C],0x10;"
    "srai  %[D],%[D],0x10;"
    "pv.add.h  %[A],%[A],%[B];"
    "pv.pack.h %[E],%[t0],%[t1];"
    "pv.pack.h %[F],%[t2],%[t3];"
    "pv.pack.h %[G],%[C],%[D];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3), [s1] "=&r" (s1), [s2] "=&r" (s2) :
      [C1] "r" (C1), [C2] "r" (C2), [C3] "r" (C3),
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
    int16_t t0, t1, t2, t3;
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
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
    "pv.sra.h  %[G],%[G],%[s1];"
    "pv.sra.h  %[H],%[H],%[s1];"
    "pv.sra.h  %[E],%[E],%[s1];"
    "pv.sra.h  %[F],%[F],%[s1];"
    "pv.extract.h  %[t0],%[H],0;"
    "pv.extract.h  %[t1],%[H],1;"
    "pv.sub.h  %[C],%[E],%[G];"
    "pv.add.h  %[D],%[E],%[G];"
    "sub %[t2],zero,%[t0];"
    "pv.pack.h %[A],%[t1],%[t2];"
    "sub %[t3],zero,%[t1];"
    "pv.pack.h %[B],%[t3],%[t0];"
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
    "srai  %[G],%[G],0x10;"
    "srai  %[H],%[H],0x10;"
    "pv.pack.h %[A],%[t0],%[t1];"
    "pv.pack.h %[B],%[t2],%[t3];"
    "pv.pack.h %[C],%[G],%[H];"
    : [A] "+&r" (A), [B] "+&r" (B), [C] "+&r" (C), [D] "+&r" (D),
      [E] "=&r" (E), [F] "=&r" (F), [G] "=&r" (G), [H] "=&r" (H),
      [t0] "=&r" (t0), [t1] "=&r" (t1), [t2] "=&r" (t2), [t3] "=&r" (t3), [s1] "=&r" (s1) :
      [C1] "r" (C1), [C2] "r" (C2), [C3] "r" (C3),
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

static inline void radix4_butterfly_last(   int16_t *pIn,
                                            int16_t *pOut,
                                            uint32_t i0,
                                            uint32_t col_id,
                                            uint32_t fftLen) {
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
    i0_store = i0 * 4 + col_id * fftLen;
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
    "addi %[s1], zero, 0x01;"
    "slli %[s1], %[s1], 0x10;"
    "addi %[s1], %[s1], 0x01;"
    "pv.sub.h  %[H],%[B],%[D];"
    "pv.add.h  %[G],%[B],%[D];"
    "pv.add.h  %[E],%[A],%[C];"
    "pv.sub.h  %[F],%[A],%[C];"
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
    /* Subtracting col_id * (fftLen >> 2U) the pointer is taken back to zero,
    then col_id * fftLen is added, so the output vectors are sequential in memory */
    i0_store = i0 * 4 + col_id * fftLen - col_id * (fftLen >> 2U);
    i1_store = i0_store + 1;
    i2_store = i1_store + 1;
    i3_store = i2_store + 1;
    *((v2s *)&pOut[i0_store * 2U]) = H;
    *((v2s *)&pOut[i1_store * 2U]) = E;
    *((v2s *)&pOut[i2_store * 2U]) = A;
    *((v2s *)&pOut[i3_store * 2U]) = B;
    #endif
}
