// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

/**
  @brief         Folding in local memory function
  @param[in]     pSrc16  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[in]     fftLen  Length of the complex input vector
  @param[in]     nPE Number of PE
  @return        none
*/

static inline void fold_radix4(__fp16 *pSrc16, uint32_t fftLen,
                               uint32_t core_id, uint32_t nPE) {
  uint32_t n2, i0, i1, i2, i3;
  uint32_t i1_store, i2_store, i3_store;
  volatile v2h A, B, C;
  n2 = fftLen >> 2U;
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, n2); i0++) {
    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;
    A = *(v2h *)&pSrc16[i1 * 2U];
    B = *(v2h *)&pSrc16[i2 * 2U];
    C = *(v2h *)&pSrc16[i3 * 2U];
    i1_store = i0 + N_BANKS;
    i2_store = i1_store + N_BANKS;
    i3_store = i2_store + N_BANKS;
    *(v2h *)&pSrc16[i1_store * 2U] = A;
    *(v2h *)&pSrc16[i2_store * 2U] = B;
    *(v2h *)&pSrc16[i3_store * 2U] = C;
  }
  mempool_log_partial_barrier(2 * WU_STRIDE, WU_STRIDE * core_id,
                              nPE * WU_STRIDE);
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
__fp16 *mempool_radix4_cfft_q16p_folded(__fp16 *pSrc16, __fp16 *pDst16,
                                         uint32_t fftLen, __fp16 *pCoef_src,
                                         __fp16 *pCoef_dst, uint32_t nPE)
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
__fp16 *mempool_radix4_cfft_q16p_folded(__fp16 *pSrc16, __fp16 *pDst16,
                                         uint32_t fftLen, __fp16 *pCoef_src,
                                         uint32_t nPE)
#endif
{

#ifdef FOLDED_TWIDDLES
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id / WU_STRIDE;
  __fp16 t0, t1, t2, t3, t4, t5;
  v2h CoSi1, CoSi2, CoSi3;
  v2h C1, C2, C3;
  uint32_t n1, n2, n2_store, i0, j, k;
  uint32_t ic, offset, wing_idx;
  __fp16 *pTmp;
#else
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id / WU_STRIDE;
  __fp16 t0, t1, t2, t3, t4, t5;
  v2h CoSi1, CoSi2, CoSi3;
  v2h C1, C2, C3;
  uint32_t n1, n2, n2_store, i0, j, k;
  uint32_t ic, offset, wing_id, bank_id;
  __fp16 *pTmp;
  uint32_t twidCoefModifier = 1U;
#endif

  if (fftLen <= N_BANKS)
    fold_radix4(pSrc16, fftLen, core_id, nPE);

  /* START OF FIRST STAGE PROCESS */
  n1 = fftLen;
  n2 = n1 >> 2U;
  n2_store = n2 >> 2U;
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, n2); i0++) {

#ifdef FOLDED_TWIDDLES
    CoSi1 = *(v2h *)&pCoef_src[2U * i0];
    CoSi2 = *(v2h *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
    CoSi3 = *(v2h *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
    if (i0 % 4 == 0) {
      ic = i0 >> 2U;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
      ic += N_BANKS;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
      ic += N_BANKS;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
    }
#else
    CoSi1 = *(v2h *)&pCoef_src[2U * i0];
    CoSi2 = *(v2h *)&pCoef_src[2U * (i0 * 2U)];
    CoSi3 = *(v2h *)&pCoef_src[2U * (i0 * 3U)];
#endif
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "fsub.h           %[t0],zero,%[t0];"
                 "fsub.h           %[t2],zero,%[t2];"
                 "fsub.h           %[t4],zero,%[t4];"
                 "pv.pack.h %[C1],%[t1],%[t0];"
                 "pv.pack.h %[C2],%[t3],%[t2];"
                 "pv.pack.h %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
    radix4_butterfly(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
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
      CoSi1 = *(v2h *)&pCoef_src[2U * j];
      CoSi2 = *(v2h *)&pCoef_src[2U * (j + 1 * N_BANKS)];
      CoSi3 = *(v2h *)&pCoef_src[2U * (j + 2 * N_BANKS)];
      if (j % 4 == 0) {
        wing_idx = j % n2;
        offset = (j / n2);
        ic = wing_idx >> 2U;
        ic += offset * n2;
        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
        ic += N_BANKS;
        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
        ic += N_BANKS;
        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
      }
#else
    bank_id = core_id / n2_store;
    wing_id = core_id % n2_store;
    offset = bank_id * n2;
    for (j = wing_id * 4; j < MIN(wing_id * 4 + 4, n2); j++) {
      ic = j * twidCoefModifier;
      CoSi1 = *(v2h *)&pCoef_src[2U * ic];
      CoSi2 = *(v2h *)&pCoef_src[2U * (ic * 2U)];
      CoSi3 = *(v2h *)&pCoef_src[2U * (ic * 3U)];
#endif
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "fsub.h           %[t0],zero,%[t0];"
                   "fsub.h           %[t2],zero,%[t2];"
                   "fsub.h           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
#ifdef FOLDED_TWIDDLES
      i0 = j;
      radix4_butterfly(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                              C2, C3);
    }
#else
      i0 = offset + j;
      radix4_butterfly(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
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
  n1 = n2;
  n2 >>= 2U;
  for (i0 = core_id * STEP; i0 < MIN(core_id * STEP + STEP, fftLen >> 2U);
       i0++) {
    radix4_butterfly_last(pSrc16, pDst16, i0);
  }
  mempool_log_partial_barrier(2 * WU_STRIDE, absolute_core_id, nPE * WU_STRIDE);
  /* END OF LAST STAGE PROCESSING */

  return pDst16;
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

void mempool_radix4_cfft_q16p_scheduler(uint32_t col_id, __fp16 *pSrc16,
                                        __fp16 *pDst16, uint32_t fftLen,
                                        __fp16 *pCoef_src, __fp16 *pCoef_dst,
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
  __fp16 *pTmp;
  int32_t t0, t1, t2, t3, t4, t5;
  v2h CoSi1, CoSi2, CoSi3;
  v2h C1, C2, C3;

  /* FIRST STAGE */
  n1 = fftLen;
  n2 = n1 >> 2U;
  n2_store = n2 >> 2U;
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
    CoSi1 = *(v2h *)&pCoef_src[2U * i0];
    CoSi2 = *(v2h *)&pCoef_src[2U * (i0 + 1 * N_BANKS)];
    CoSi3 = *(v2h *)&pCoef_src[2U * (i0 + 2 * N_BANKS)];
    if (i0 % 4 == 0) {
      ic = i0 / 4;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
      ic += N_BANKS;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
      ic += N_BANKS;
      *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
      *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
    }
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "fsub.h           %[t0],zero,%[t0];"
                 "fsub.h           %[t2],zero,%[t2];"
                 "fsub.h           %[t4],zero,%[t4];"
                 "pv.pack.h %[C1],%[t1],%[t0];"
                 "pv.pack.h %[C2],%[t3],%[t2];"
                 "pv.pack.h %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      __fp16 *pIn = pSrc16 + idx_row * (N_BANKS * 8);
      __fp16 *pOut = pDst16 + idx_row * (N_BANKS * 8);
      radix4_butterfly(pIn, pOut, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
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
      CoSi1 = *(v2h *)&pCoef_src[2U * (j)];
      CoSi2 = *(v2h *)&pCoef_src[2U * (j + 1 * N_BANKS)];
      CoSi3 = *(v2h *)&pCoef_src[2U * (j + 2 * N_BANKS)];
      if (j % 4 == 0) {

        wing_idx = j % n2;
        offset = (j / n2);
        ic = wing_idx >> 2U;
        ic += offset * n2;

        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi1;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi1;
        ic += N_BANKS;
        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi2;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi2;
        ic += N_BANKS;
        *((v2h *)&pCoef_dst[2U * (ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic)]) = CoSi3;
        *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic)]) = CoSi3;
      }
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "fsub.h           %[t0],zero,%[t0];"
                   "fsub.h           %[t2],zero,%[t2];"
                   "fsub.h           %[t4],zero,%[t4];"
                   "pv.pack.h %[C1],%[t1],%[t0];"
                   "pv.pack.h %[C2],%[t3],%[t2];"
                   "pv.pack.h %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
      for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        __fp16 *pIn = pSrc16 + idx_row * (N_BANKS * 8);
        __fp16 *pOut = pDst16 + idx_row * (N_BANKS * 8);
        radix4_butterfly(pIn, pOut, j, n2, CoSi1, CoSi2, CoSi3, C1, C2,
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
  }

  /*  LAST STAGE */
  n1 = n2;
  n2 >>= 2U;
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      __fp16 *pIn = pSrc16 + idx_row * (N_BANKS * 8);
      __fp16 *pOut = pDst16 + idx_row * (N_BANKS * 8);
      radix4_butterfly_last(pIn, pOut, i0);
    }
  }
  pTmp = pSrc16;
  pSrc16 = pDst16;
  pDst16 = pTmp;
  mempool_log_partial_barrier(2, absolute_core_id, nPE);

  mempool_stop_benchmark();
  mempool_start_benchmark();

  /* BITREVERSAL */
  // Bitreversal stage stores in the sequential addresses
  if (bitReverseFlag) {
#ifdef BITREVERSETABLE
    uint16_t *ptr1 = (uint16_t *)(pSrc16 + 2 * col_id * (fftLen >> 2U));
    uint16_t *ptr2 = (uint16_t *)(pDst16 + 2 * col_id * (3 * (fftLen >> 2)));
    for (j = 2 * core_id; j < bitReverseLen; j += 2 * nPE) {
      v2h addr, tmpa, tmpb;
      addr = __SRA2(*(v2h *)&pBitRevTable[j], ((v2h){2, 2}));
      for (int32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        int32_t a0 = addr[0] / 4 + (addr[0] % 4) * N_BANKS;
        int32_t a1 = addr[1] / 4 + (addr[0] % 4) * N_BANKS;
        tmpa = *(v2h *)&ptr1[a0 + idx_row * (N_BANKS * 8)];
        tmpb = *(v2h *)&ptr1[a1 + idx_row * (N_BANKS * 8)];
        *((v2h *)&ptr2[addr[0] + idx_row * (N_BANKS * 8)]) = tmpb;
        *((v2h *)&ptr2[addr[1] + idx_row * (N_BANKS * 8)]) = tmpa;
      }
    }
#else
    uint16_t *ptr1 = (uint16_t *)(pSrc16 + 2 * col_id * (fftLen >> 2U));
    uint16_t *ptr2 = (uint16_t *)(pDst16 + 2 * col_id * (3 * (fftLen >> 2)));
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
}
