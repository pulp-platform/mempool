// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

void mempool_radix4_cfft_q16p_xpulpimg(int16_t *pSrc16, uint32_t fftLen,
                                       const int16_t *pCoef16,
                                       uint32_t twidCoefModifier,
                                       uint32_t nPE) {
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % nPE;
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  uint32_t n1, n2, ic, i0, j, k;
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
    t1 = (int16_t)CoSi1[0];
    t3 = (int16_t)CoSi2[0];
    t5 = (int16_t)CoSi3[0];
    t0 = (int16_t)CoSi1[1];
    t2 = (int16_t)CoSi2[1];
    t4 = (int16_t)CoSi3[1];
    C1 = __PACK2(t1, -t0);
    C2 = __PACK2(t3, -t2);
    C3 = __PACK2(t5, -t4);
#else
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "sub           %[t0],zero,%[t0];"
                 "sub           %[t2],zero,%[t2];"
                 "sub           %[t4],zero,%[t4];"
                 "pv.pack %[C1],%[t1],%[t0];"
                 "pv.pack %[C2],%[t3],%[t2];"
                 "pv.pack %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
#endif
    radix4_butterfly_first(pSrc16, pSrc16, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
                           C3);
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
    for (j = butt_id * step; j < MIN(butt_id * step + step, n2); j++) {
      /*  Twiddle coefficients index modifier */
      ic = twidCoefModifier * j;
      CoSi1 = *(v2s *)&pCoef16[ic * 2U];
      CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
      CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
#ifndef ASM
      t1 = (int16_t)CoSi1[0];
      t3 = (int16_t)CoSi2[0];
      t5 = (int16_t)CoSi3[0];
      t0 = (int16_t)CoSi1[1];
      t2 = (int16_t)CoSi2[1];
      t4 = (int16_t)CoSi3[1];
      C1 = __PACK2(t1, -t0);
      C2 = __PACK2(t3, -t2);
      C3 = __PACK2(t5, -t4);
#else
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "sub           %[t0],zero,%[t0];"
                   "sub           %[t2],zero,%[t2];"
                   "sub           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
#endif
      /*  Butterfly implementation */
      for (i0 = offset + j; i0 < fftLen; i0 += ((nPE + n2 - 1) / n2) * n1) {
        radix4_butterfly_middle(pSrc16, pSrc16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                                C2, C3);
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
  for (i0 = core_id * step * n1; i0 < MIN((core_id * step + step) * n1, fftLen);
       i0 += n1) {
    radix4_butterfly_last(pSrc16, pSrc16, i0);
  }
  mempool_log_barrier(2, absolute_core_id);
  /* END OF LAST STAGE PROCESSING */
  return;
}

void mempool_radix4by2_cfft_q16p(int16_t *pSrc, uint32_t fftLen,
                                 const int16_t *pCoef, uint32_t nPE) {

  uint32_t i;
  uint32_t n2, step;
  v2s pa, pb;

  uint32_t l;
  v2s CoSi;
  v2s a, b, t;
  int16_t testa, testb;
  uint32_t core_id = mempool_get_core_id();

  n2 = fftLen >> 1;
  step = (n2 + nPE - 1) / nPE;
  for (i = core_id * step; i < MIN(core_id * step + step, n2); i++) {

    CoSi = *(v2s *)&pCoef[i * 2];
    l = i + n2;
    a = __SRA2(*(v2s *)&pSrc[2 * i], ((v2s){1, 1}));
    b = __SRA2(*(v2s *)&pSrc[2 * l], ((v2s){1, 1}));
    t = __SUB2(a, b);
    *((v2s *)&pSrc[i * 2]) = __SRA2(__ADD2(a, b), ((v2s){1, 1}));

    testa = (int16_t)(__DOTP2(t, CoSi) >> 16);
    testb = (int16_t)(__DOTP2(t, __PACK2(-CoSi[1], CoSi[0])) >> 16);
    *((v2s *)&pSrc[l * 2]) = __PACK2(testa, testb);
  }
  mempool_log_barrier(2, core_id);

  if (nPE > 1) {
    if (core_id < nPE / 2) {
      // first col
      mempool_radix4_cfft_q16p_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U,
                                        nPE / 2);
    } else {
      // second col
      mempool_radix4_cfft_q16p_xpulpimg(pSrc + fftLen, n2, (int16_t *)pCoef, 2U,
                                        nPE - nPE / 2);
    }
  } else {
    // first col
    mempool_radix4_cfft_q16p_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U, nPE);
    // second col
    mempool_radix4_cfft_q16p_xpulpimg(pSrc + fftLen, n2, (int16_t *)pCoef, 2U,
                                      nPE);
  }

  for (i = core_id * step; i < MIN(core_id * step + step, n2); i++) {

    pa = *(v2s *)&pSrc[4 * i];
    pb = *(v2s *)&pSrc[4 * i + 2];

    pa = __SLL2(pa, ((v2s){1, 1}));
    pb = __SLL2(pb, ((v2s){1, 1}));

    *((v2s *)&pSrc[4 * i]) = pa;
    *((v2s *)&pSrc[4 * i + 2]) = pb;
  }
  mempool_log_barrier(2, core_id);
  return;
}

/**
  @brief         Folding in local memory function
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     nPE Number of PE
  @return        none
*/

static inline void fold_radix4(int16_t *pSrc16, uint32_t fftLen, uint32_t nPE) {
  uint32_t n2, i0, i1, i2, i3;
  uint32_t i1_store, i2_store, i3_store;
  volatile v2s A, B, C;
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % 4U;
  n2 = fftLen >> 2U;
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, n2); i0++) {
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    i1_store = i0 + N_BANKS;
    i2_store = i1_store + N_BANKS;
    i3_store = i2_store + N_BANKS;
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      A = *(v2s *)&pSrc16[i1 * 2U + idx_row * (8 * N_BANKS)];
      B = *(v2s *)&pSrc16[i2 * 2U + idx_row * (8 * N_BANKS)];
      C = *(v2s *)&pSrc16[i3 * 2U + idx_row * (8 * N_BANKS)];
      *(v2s *)&pSrc16[i1_store * 2U + idx_row * (8 * N_BANKS)] = A;
      *(v2s *)&pSrc16[i2_store * 2U + idx_row * (8 * N_BANKS)] = B;
      *(v2s *)&pSrc16[i3_store * 2U + idx_row * (8 * N_BANKS)] = C;
    }
  }
  mempool_log_partial_barrier(2 * WU_STRIDE, WU_STRIDE * absolute_core_id,
                              nPE * WU_STRIDE);
  return;
}

#ifdef FOLDED_TWIDDLES
/**
  @brief         Full FFT butterfly
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[out]    pDst16  points to output buffer of 16b data, Re and Im parts
  are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     pCoef_src Twiddle coefficients vector
  @param[in]     pCoef_dst Auxiliary twiddle coefficients vector
  @param[in]     nPE Number of PE
  @return        pointer to output vector
*/
void mempool_radix4_cfft_q16p_folded(int16_t *pSrc16, int16_t *pDst16,
                                     uint32_t fftLen, int16_t *pCoef_src,
                                     int16_t *pCoef_dst, uint32_t nPE)
#else
/**
  Twiddles are not folded in memory
  @brief         Full FFT butterfly
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[out]    pDst16  points to output buffer of 16b data, Re and Im parts
  are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     pCoef_src Twiddle coefficients vector
  @param[in]     nPE Number of PE
  @return        pointer to output vector
*/
void mempool_radix4_cfft_q16p_folded(int16_t *pSrc16, int16_t *pDst16,
                                     uint32_t fftLen, int16_t *pCoef_src,
                                     uint32_t nPE)
#endif
{

#ifdef FOLDED_TWIDDLES
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id / WU_STRIDE;
  int16_t t0, t1, t2, t3, t4, t5;
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  uint32_t n1, n2, n2_store, i0, j, k;
  uint32_t ic, offset, wing_idx;
  int16_t *pTmp;
#else
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id / WU_STRIDE;
  int16_t t0, t1, t2, t3, t4, t5;
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  uint32_t n1, n2, n2_store, i0, j, k;
  uint32_t ic, offset, wing_id, bank_id;
  int16_t *pTmp;
  uint32_t twidCoefModifier = 1U;
#endif

  /* START OF FIRST STAGE PROCESS */
  n1 = fftLen;
  n2 = n1 >> 2U;
  n2_store = n2 >> 2U;
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, n2); i0++) {

#ifdef FOLDED_TWIDDLES
    CoSi1 = *(v2s *)&pCoef_src[2U * i0];
    CoSi2 = *(v2s *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
    CoSi3 = *(v2s *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
    if (i0 % 4 == 0) {
      ic = i0 >> 2U;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
      ic += N_BANKS;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
      ic += N_BANKS;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
    }
#else
    CoSi1 = *(v2s *)&pCoef_src[2U * i0];
    CoSi2 = *(v2s *)&pCoef_src[2U * (i0 * 2U)];
    CoSi3 = *(v2s *)&pCoef_src[2U * (i0 * 3U)];
#endif

#ifndef ASM
    t1 = (int16_t)CoSi1[0];
    t3 = (int16_t)CoSi2[0];
    t5 = (int16_t)CoSi3[0];
    t0 = (int16_t)CoSi1[1];
    t2 = (int16_t)CoSi2[1];
    t4 = (int16_t)CoSi3[1];
    C1 = __PACK2(t1, -t0);
    C2 = __PACK2(t3, -t2);
    C3 = __PACK2(t5, -t4);
#else
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "sub           %[t0],zero,%[t0];"
                 "sub           %[t2],zero,%[t2];"
                 "sub           %[t4],zero,%[t4];"
                 "pv.pack %[C1],%[t1],%[t0];"
                 "pv.pack %[C2],%[t3],%[t2];"
                 "pv.pack %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
#endif
    radix4_butterfly_first(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
                           C3);
  }
  pTmp = pSrc16;
  pSrc16 = pDst16;
  pDst16 = pTmp;
#ifdef FOLDED_TWIDDLES
  pTmp = pCoef_src;
  pCoef_src = pCoef_dst;
  pCoef_dst = pTmp;
#else
  twidCoefModifier <<= 2U;
#endif
  mempool_log_partial_barrier(2 * WU_STRIDE, absolute_core_id, nPE * WU_STRIDE);
  /* END OF FIRST STAGE PROCESSING */

  /* START OF MIDDLE STAGE PROCESS */
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {
    n1 = n2;
    n2 >>= 2U;
    n2_store = n2 >> 2U;

#ifdef FOLDED_TWIDDLES
    for (j = core_id * STEP; j < core_id * STEP + STEP; j++) {
      CoSi1 = *(v2s *)&pCoef_src[2U * j];
      CoSi2 = *(v2s *)&pCoef_src[2U * (j + 1 * N_BANKS)];
      CoSi3 = *(v2s *)&pCoef_src[2U * (j + 2 * N_BANKS)];
      if (j % 4 == 0) {
        wing_idx = j % n2;
        offset = (j / n2);
        ic = wing_idx >> 2U;
        ic += offset * n2;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
        ic += N_BANKS;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
        ic += N_BANKS;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
      }
#else
    bank_id = core_id / n2_store;
    wing_id = core_id % n2_store;
    offset = bank_id * n2;
    for (j = wing_id * 4; j < MIN(wing_id * 4 + 4, n2); j++) {
      ic = j * twidCoefModifier;
      CoSi1 = *(v2s *)&pCoef_src[2U * ic];
      CoSi2 = *(v2s *)&pCoef_src[2U * (ic * 2U)];
      CoSi3 = *(v2s *)&pCoef_src[2U * (ic * 3U)];
#endif
#ifndef ASM
      t1 = (int16_t)CoSi1[0];
      t3 = (int16_t)CoSi2[0];
      t5 = (int16_t)CoSi3[0];
      t0 = (int16_t)CoSi1[1];
      t2 = (int16_t)CoSi2[1];
      t4 = (int16_t)CoSi3[1];
      C1 = __PACK2(t1, -t0);
      C2 = __PACK2(t3, -t2);
      C3 = __PACK2(t5, -t4);
#else
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "sub           %[t0],zero,%[t0];"
                   "sub           %[t2],zero,%[t2];"
                   "sub           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
#endif
#ifdef FOLDED_TWIDDLES
      i0 = j;
      radix4_butterfly_middle(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                              C2, C3);
    }
#else
      i0 = offset + j;
      radix4_butterfly_middle(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                              C2, C3);
    }
#endif
    pTmp = pSrc16;
    pSrc16 = pDst16;
    pDst16 = pTmp;
#ifdef FOLDED_TWIDDLES
    pTmp = pCoef_src;
    pCoef_src = pCoef_dst;
    pCoef_dst = pTmp;
#else
    twidCoefModifier <<= 2U;
#endif
    mempool_log_partial_barrier(2 * WU_STRIDE, absolute_core_id,
                                nPE * WU_STRIDE);
  }
  /* END OF MIDDLE STAGE PROCESSING */

  /* START OF LAST STAGE PROCESSING */
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, fftLen >> 2U);
       i0++) {
    radix4_butterfly_last(pSrc16, pDst16, i0);
  }
  mempool_log_partial_barrier(2 * WU_STRIDE, absolute_core_id, nPE * WU_STRIDE);
  /* END OF LAST STAGE PROCESSING */

  return;
}

/**
  SCHEDULER OF MULTIPLE FOLDED FFTS
  Memory:

  1st row of FFTS

  col_idx1     col_idx2     col_idx3
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...

  2nd row of FFTS

  col_idx1     col_idx2     col_idx3
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...
  xxxxxxxxxxxx xxxxxxxxxxxx xxxxxxxxxxxx ...

  ...

  @brief         Scheduler of folded FFTs
  @param[in]     column index of the current FFT
  @param[in]     pSrc16  input buffer of 16b data, Re and Im are interleaved
  @param[out]    pDst16  output buffer of 16b data, Re and Im are interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     pCoef_src Twiddle coefficients vector
  @param[in]     pCoef_dst Twiddle coefficients vector
  @param[in]     pBitRevTable Bitreversal table
  @param[in]     bitReverseLen Length of bitreversal table
  @param[in]     bitReverseFlag Flag for bitreversal
  @param[in]     nPE Number of PE
  @return        void
*/

void mempool_radix4_cfft_q16p_scheduler(uint32_t col_id, int16_t *pSrc16,
                                        int16_t *pDst16, uint32_t fftLen,
                                        int16_t *pCoef_src, int16_t *pCoef_dst,
                                        __attribute__((unused))
                                        uint16_t *pBitRevTable,
                                        __attribute__((unused))
                                        uint16_t bitReverseLen,
                                        uint8_t bitReverseFlag, uint32_t nPE) {

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (fftLen >> 4U);

  uint32_t n1, n2, i0, ic, j, k;
  uint32_t n2_store;
  uint32_t offset, wing_idx;
  int16_t *pTmp;
  int32_t t0, t1, t2, t3, t4, t5;
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;

  /* FIRST STAGE */
  n1 = fftLen;
  n2 = n1 >> 2U;
  n2_store = n2 >> 2U;
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
    CoSi1 = *(v2s *)&pCoef_src[2U * i0];
    CoSi2 = *(v2s *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
    CoSi3 = *(v2s *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
    if (i0 % 4 == 0) {
      ic = i0 / 4;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
      ic += N_BANKS;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
      ic += N_BANKS;
      *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
      *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
    }
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "sub           %[t0],zero,%[t0];"
                 "sub           %[t2],zero,%[t2];"
                 "sub           %[t4],zero,%[t4];"
                 "pv.pack %[C1],%[t1],%[t0];"
                 "pv.pack %[C2],%[t3],%[t2];"
                 "pv.pack %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      int16_t *pIn = pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * fftLen;
      int16_t *pOut = pDst16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
      radix4_butterfly_first(pIn, pOut, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
                             C3);
    }
  }
  pTmp = pSrc16;
  pSrc16 = pDst16;
  pDst16 = pTmp;
  pTmp = pCoef_src;
  pCoef_src = pCoef_dst;
  pCoef_dst = pTmp;
  mempool_log_partial_barrier(2, absolute_core_id, nPE);

  /* MIDDLE STAGE */
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {
    n1 = n2;
    n2 >>= 2U;
    n2_store = n2 >> 2U;
    for (j = core_id * 4; j < core_id * 4 + 4; j++) {
      CoSi1 = *(v2s *)&pCoef_src[2U * (j)];
      CoSi2 = *(v2s *)&pCoef_src[2U * (j + 1 * N_BANKS)];
      CoSi3 = *(v2s *)&pCoef_src[2U * (j + 2 * N_BANKS)];
      if (j % 4 == 0) {
        wing_idx = j % n2;
        offset = (j / n2);
        ic = wing_idx >> 2U;
        ic += offset * n2;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
        ic += N_BANKS;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
        ic += N_BANKS;
        *((v2s *)&pCoef_dst[2U * (ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
        *((v2s *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
      }
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "sub           %[t0],zero,%[t0];"
                   "sub           %[t2],zero,%[t2];"
                   "sub           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
      for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        int16_t *pIn =
            pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
        int16_t *pOut =
            pDst16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
        radix4_butterfly_middle(pIn, pOut, j, n2, CoSi1, CoSi2, CoSi3, C1, C2,
                                C3);
      }
    }
    pTmp = pSrc16;
    pSrc16 = pDst16;
    pDst16 = pTmp;
    pTmp = pCoef_src;
    pCoef_src = pCoef_dst;
    pCoef_dst = pTmp;
    mempool_log_partial_barrier(2, absolute_core_id, N_FFTs_COL * nPE);
  }

  /*  LAST STAGE */
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      int16_t *pIn =
          pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
      int16_t *pOut =
          pDst16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
      radix4_butterfly_last(pIn, pOut, i0);
    }
  }
  pTmp = pSrc16;
  pSrc16 = pDst16;
  pDst16 = pTmp;
  mempool_log_partial_barrier(2, absolute_core_id, N_FFTs_COL * nPE);
  mempool_stop_benchmark();
  mempool_start_benchmark();
  /* BITREVERSAL */
  // Bitreversal stage stores in the sequential addresses
  if (bitReverseFlag) {
#ifdef BITREVERSETABLE
    pSrc16 = pSrc16 + 2 * col_id * (fftLen / 4);
    pDst16 = pDst16 + 2 * col_id * fftLen;
    for (j = 8 * core_id; j < bitReverseLen; j += 8 * nPE) {
      uint32_t addr1, addr2, addr3, addr4;
      uint32_t tmpa1, tmpa2, tmpa3, tmpa4;
      uint32_t tmpb1, tmpb2, tmpb3, tmpb4;
      uint32_t a1, a2, a3, a4;
      uint32_t b1, b2, b3, b4;
      uint32_t a1_load, a2_load, a3_load, a4_load;
      uint32_t b1_load, b2_load, b3_load, b4_load;
      uint32_t s2 = 0x00020002;
      addr1 = *(uint32_t *)&pBitRevTable[j];
      addr2 = *(uint32_t *)&pBitRevTable[j + 2];
      addr3 = *(uint32_t *)&pBitRevTable[j + 4];
      addr4 = *(uint32_t *)&pBitRevTable[j + 6];
      asm volatile(
          "pv.sra.h  %[addr1],%[addr1],%[s2];"
          "pv.sra.h  %[addr2],%[addr2],%[s2];"
          "pv.sra.h  %[addr3],%[addr3],%[s2];"
          "pv.sra.h  %[addr4],%[addr4],%[s2];"
          "pv.extract.h  %[a1],%[addr1],0;"
          "pv.extract.h  %[a2],%[addr2],0;"
          "pv.extract.h  %[a3],%[addr3],0;"
          "pv.extract.h  %[a4],%[addr4],0;"
          "pv.extract.h  %[b1],%[addr1],1;"
          "pv.extract.h  %[b2],%[addr2],1;"
          "pv.extract.h  %[b3],%[addr3],1;"
          "pv.extract.h  %[b4],%[addr4],1;"
          : [a1] "=r"(a1), [a2] "=r"(a2), [a3] "=r"(a3), [a4] "=r"(a4),
            [b1] "=r"(b1), [b2] "=r"(b2), [b3] "=r"(b3), [b4] "=r"(b4),
            [addr1] "+&r"(addr1), [addr2] "+&r"(addr2),
            [addr3] "+&r"(addr3), [addr4] "+&r"(addr4)
          : [s2] "r"(s2)
          :);
      // Compute the local addresses from the natural order ones
      a1_load = (a1 % 4) * 2 * N_BANKS + 2 * (a1 / 4);
      a2_load = (a2 % 4) * 2 * N_BANKS + 2 * (a2 / 4);
      a3_load = (a3 % 4) * 2 * N_BANKS + 2 * (a3 / 4);
      a4_load = (a4 % 4) * 2 * N_BANKS + 2 * (a4 / 4);
      b1_load = (b1 % 4) * 2 * N_BANKS + 2 * (b1 / 4);
      b2_load = (b2 % 4) * 2 * N_BANKS + 2 * (b2 / 4);
      b3_load = (b3 % 4) * 2 * N_BANKS + 2 * (b3 / 4);
      b4_load = (b4 % 4) * 2 * N_BANKS + 2 * (b4 / 4);
      for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        uint16_t *ptr1 = (uint16_t *)(pSrc16 + idx_row * (N_BANKS * 8));
        uint16_t *ptr2 = (uint16_t *)(pDst16 + idx_row * (N_BANKS * 8));
        // Load at address a
        tmpa1 = *(uint32_t *)&ptr1[a1_load];
        tmpa2 = *(uint32_t *)&ptr1[a2_load];
        tmpa3 = *(uint32_t *)&ptr1[a3_load];
        tmpa4 = *(uint32_t *)&ptr1[a4_load];
        // Load at address b
        tmpb1 = *(uint32_t *)&ptr1[b1_load];
        tmpb2 = *(uint32_t *)&ptr1[b2_load];
        tmpb3 = *(uint32_t *)&ptr1[b3_load];
        tmpb4 = *(uint32_t *)&ptr1[b4_load];
        // Swap a with b
        *((uint32_t *)&ptr2[b1]) = tmpa1;
        *((uint32_t *)&ptr2[b2]) = tmpa2;
        *((uint32_t *)&ptr2[b3]) = tmpa3;
        *((uint32_t *)&ptr2[b4]) = tmpa4;
        // Swap b with a
        *((uint32_t *)&ptr2[a1]) = tmpb1;
        *((uint32_t *)&ptr2[a2]) = tmpb2;
        *((uint32_t *)&ptr2[a3]) = tmpb3;
        *((uint32_t *)&ptr2[a4]) = tmpb4;
      }
    }
#else
    uint16_t *ptr1 = (uint16_t *)(pSrc16 + 2 * col_id * (fftLen / 4));
    uint16_t *ptr2 = (uint16_t *)(pDst16 + 2 * col_id * fftLen);
    for (j = core_id * 16; j < MIN(core_id * 16 + 16, fftLen >> 2U); j += 4) {
      uint32_t idx0 = j;
      uint32_t idx1 = j + 1;
      uint32_t idx2 = j + 2;
      uint32_t idx3 = j + 3;
      uint32_t idx_result0 = 0;
      uint32_t idx_result1 = 0;
      uint32_t idx_result2 = 0;
      uint32_t idx_result3 = 0;
      for (k = 0; k < LOG2; k++) {
        idx_result0 = (idx_result0 << 1U) | (idx0 & 1U);
        idx_result1 = (idx_result1 << 1U) | (idx1 & 1U);
        idx_result2 = (idx_result2 << 1U) | (idx2 & 1U);
        idx_result3 = (idx_result3 << 1U) | (idx3 & 1U);
        idx0 = idx0 >> 1U;
        idx1 = idx1 >> 1U;
        idx2 = idx2 >> 1U;
        idx3 = idx3 >> 1U;
      }
      for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        uint32_t addr_src0 = (idx0 / 4) + (idx0 % 4) * N_BANKS;
        uint32_t addr_src1 = (idx1 / 4) + (idx1 % 4) * N_BANKS;
        uint32_t addr_src2 = (idx2 / 4) + (idx2 % 4) * N_BANKS;
        uint32_t addr_src3 = (idx3 / 4) + (idx3 % 4) * N_BANKS;
        uint32_t addr_dst0 = idx_result0;
        uint32_t addr_dst1 = idx_result1;
        uint32_t addr_dst2 = idx_result2;
        uint32_t addr_dst3 = idx_result3;
        addr_src0 += idx_row * (N_BANKS * 8);
        addr_src1 += idx_row * (N_BANKS * 8);
        addr_src2 += idx_row * (N_BANKS * 8);
        addr_src3 += idx_row * (N_BANKS * 8);
        addr_dst0 += idx_row * (N_BANKS * 8);
        addr_dst1 += idx_row * (N_BANKS * 8);
        addr_dst2 += idx_row * (N_BANKS * 8);
        addr_dst3 += idx_row * (N_BANKS * 8);
        *((uint32_t *)&ptr2[addr_dst0]) = (uint32_t)ptr1[addr_src0];
        *((uint32_t *)&ptr2[addr_dst1]) = (uint32_t)ptr1[addr_src1];
        *((uint32_t *)&ptr2[addr_dst2]) = (uint32_t)ptr1[addr_src2];
        *((uint32_t *)&ptr2[addr_dst3]) = (uint32_t)ptr1[addr_src3];
      }
    }
#endif
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
  return;
}
