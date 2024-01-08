// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"
#define MIN(x, y) (((x) < (y)) ? (x) : (y))

// CoSi: (Si, Co) -> C: (Co, -Si)
#define SHUFFLE_TWIDDLEFACT                                                    \
  asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"                               \
               "pv.extract.h  %[t3],%[CoSi2],0;"                               \
               "pv.extract.h  %[t5],%[CoSi3],0;"                               \
               "pv.extract.h  %[t0],%[CoSi1],1;"                               \
               "pv.extract.h  %[t2],%[CoSi2],1;"                               \
               "pv.extract.h  %[t4],%[CoSi3],1;"                               \
               "xor           %[t0],%[t0],%[neg_mask];"                        \
               "xor           %[t2],%[t2],%[neg_mask];"                        \
               "xor           %[t4],%[t4],%[neg_mask];"                        \
               "pv.pack   %[C1],%[t1],%[t0];"                                  \
               "pv.pack   %[C2],%[t3],%[t2];"                                  \
               "pv.pack   %[C3],%[t5],%[t4];"                                  \
               : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),  \
                 [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),               \
                 [t4] "=&r"(t4), [t5] "=&r"(t5)                                \
               : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3),   \
                 [neg_mask] "r"(0x00008000)                                    \
               :);

#ifdef FOLDED_TWIDDLES

#define LOAD_STORE_TWIDDLEFACT                                                 \
  CoSi1 = *(v2h *)&pCoef_src[2U * ic];                                         \
  CoSi2 = *(v2h *)&pCoef_src[2U * (ic + 1 * N_BANKS)];                         \
  CoSi3 = *(v2h *)&pCoef_src[2U * (ic + 2 * N_BANKS)];                         \
  if (ic % 4 == 0) {                                                           \
    *((v2h *)&pCoef_dst[2U * (ic_store)]) = CoSi1;                             \
    *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic_store)]) = CoSi1;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic_store)]) = CoSi1;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic_store)]) = CoSi1;              \
    ic_store += N_BANKS;                                                       \
    *((v2h *)&pCoef_dst[2U * (ic_store)]) = CoSi2;                             \
    *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic_store)]) = CoSi2;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic_store)]) = CoSi2;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic_store)]) = CoSi2;              \
    ic_store += N_BANKS;                                                       \
    *((v2h *)&pCoef_dst[2U * (ic_store)]) = CoSi3;                             \
    *((v2h *)&pCoef_dst[2U * (n2_store * 1 + ic_store)]) = CoSi3;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 2 + ic_store)]) = CoSi3;              \
    *((v2h *)&pCoef_dst[2U * (n2_store * 3 + ic_store)]) = CoSi3;              \
  }

#else
#define LOAD_STORE_TWIDDLEFACT                                                 \
  CoSi1 = *(v2h *)&pCoef_src[2U * ic];                                         \
  CoSi2 = *(v2h *)&pCoef_src[2U * (ic * 2U)];                                  \
  CoSi3 = *(v2h *)&pCoef_src[2U * (ic * 3U)];
#endif

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
void mempool_radix4_cfft_f16p_folded(__fp16 *pSrc16, __fp16 *pDst16,
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
void mempool_radix4_cfft_f16p_folded(__fp16 *pSrc16, __fp16 *pDst16,
                                     uint32_t fftLen, __fp16 *pCoef_src,
                                     uint32_t nPE)
#endif
{

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id;
  __fp16 t0, t1, t2, t3, t4, t5;
  v2h CoSi1, CoSi2, CoSi3;
  v2h C1, C2, C3;
#ifdef FOLDED_TWIDDLES
  uint32_t n1, n2, n2_store;
  uint32_t i0, k, ic, ic_store;
  __fp16 *pTmp;
#else
  uint32_t n1, n2;
  uint32_t i0, k, ic;
  __fp16 *pTmp;
  uint32_t twidCoefModifier = 1U;
#endif

  /* START OF FIRST STAGE PROCESSING */
  n1 = fftLen;
  n2 = n1 >> 2U;
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {

#ifdef FOLDED_TWIDDLES
    ic = i0;
    ic_store = ic >> 2U;
    n2_store = n2 >> 2U;
#else
    ic = i0;
#endif
    LOAD_STORE_TWIDDLEFACT;
    SHUFFLE_TWIDDLEFACT;
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
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
  /* END OF FIRST STAGE PROCESSING */

  /* START OF MIDDLE STAGE PROCESSING */
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {
    n1 = n2;
    n2 >>= 2U;
    for (i0 = core_id * 4; i0 < core_id * 4 + 4; i0++) {
#ifdef FOLDED_TWIDDLES
      ic = i0;
      // (ic % n2) / 4 take only every 4th index in the wing
      // (ic / n2) * n2 shift of the wing size
      ic_store = ((ic % n2) >> 2) + (ic / n2) * n2;
      n2_store = n2 >> 2U;
#else
      ic = (i0 % n2) * twidCoefModifier;
#endif
      LOAD_STORE_TWIDDLEFACT;
      SHUFFLE_TWIDDLEFACT;
      radix4_butterfly_middle(pSrc16, pDst16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                              C2, C3);
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
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
  }
  /* END OF MIDDLE STAGE PROCESSING */

  /* START OF LAST STAGE PROCESSING */
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, fftLen >> 2U); i0++) {
    radix4_butterfly_last(pSrc16, pDst16, i0);
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
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

void mempool_radix4_cfft_f16p_scheduler(
    __fp16 *pSrc16, __fp16 *pDst16, uint32_t fftLen, __fp16 *pCoef_src,
    __fp16 *pCoef_dst, __attribute__((unused)) uint16_t *pBitRevTable,
    __attribute__((unused)) uint16_t bitReverseLen, uint8_t bitReverseFlag,
    uint32_t nPE) {

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (fftLen >> 4U);
  uint32_t col_id = absolute_core_id / (fftLen >> 4U);

  __fp16 t0, t1, t2, t3, t4, t5;
  v2h CoSi1, CoSi2, CoSi3;
  v2h C1, C2, C3;
#ifdef FOLDED_TWIDDLES
  uint32_t n1, n2, n2_store;
  uint32_t i0, k, ic, ic_store;
#else
  uint32_t n1, n2;
  uint32_t i0, k, ic;
  uint32_t twidCoefModifier = 1U;
#endif
  __fp16 *pTmp;

  /* FIRST STAGE */
  n1 = fftLen;
  n2 = n1 >> 2U;
  for (i0 = core_id * 4; i0 < MIN(core_id * 4 + 4, n2); i0++) {
    ic = i0;
#ifdef FOLDED_TWIDDLES
    ic_store = ic >> 2U;
    n2_store = n2 >> 2U;
#endif
    LOAD_STORE_TWIDDLEFACT;
    SHUFFLE_TWIDDLEFACT;
    for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
      __fp16 *pIn = pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * fftLen;
      __fp16 *pOut =
          pDst16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
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
    for (i0 = core_id * 4; i0 < core_id * 4 + 4; i0++) {
#ifdef FOLDED_TWIDDLES
      ic = i0;
      ic_store = ((ic % n2) >> 2) + (ic / n2) * n2;
      n2_store = n2 >> 2U;
#else
      ic = (i0 % n2) * twidCoefModifier;
#endif
      LOAD_STORE_TWIDDLEFACT;
      SHUFFLE_TWIDDLEFACT;

      for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
        __fp16 *pIn =
            pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
        __fp16 *pOut =
            pDst16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
        radix4_butterfly_middle(pIn, pOut, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
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
      __fp16 *pIn =
          pSrc16 + idx_row * (N_BANKS * 8) + 2 * col_id * (fftLen / 4);
      __fp16 *pOut =
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
    for (ic = 8 * core_id; ic < bitReverseLen; ic += 8 * nPE) {
      uint32_t addr1, addr2, addr3, addr4;
      uint32_t tmpa1, tmpa2, tmpa3, tmpa4;
      uint32_t tmpb1, tmpb2, tmpb3, tmpb4;
      uint32_t a1, a2, a3, a4;
      uint32_t b1, b2, b3, b4;
      uint32_t a1_load, a2_load, a3_load, a4_load;
      uint32_t b1_load, b2_load, b3_load, b4_load;
      uint32_t s2 = 0x00020002;
      addr1 = *(uint32_t *)&pBitRevTable[ic];
      addr2 = *(uint32_t *)&pBitRevTable[ic + 2];
      addr3 = *(uint32_t *)&pBitRevTable[ic + 4];
      addr4 = *(uint32_t *)&pBitRevTable[ic + 6];
      asm volatile("pv.sra.h  %[addr1],%[addr1],%[s2];"
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
    for (ic = core_id * 16; ic < MIN(core_id * 16 + 16, fftLen >> 2U);
         ic += 4) {
      uint32_t idx0 = ic;
      uint32_t idx1 = ic + 1;
      uint32_t idx2 = ic + 2;
      uint32_t idx3 = ic + 3;
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
