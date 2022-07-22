// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

/* Mempool runtime libraries */
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

/* CFFT mempool libraries */
#include "define.h"
#include "mempool_cfft_q16_twiddleCoef.h"
#include "mempool_cfft_q16_BitRevIndexTable.h"

#ifdef SINGLE
#include "mempool_cfft_q16s.h"
#endif
#ifdef PARALLEL
#include "mempool_cfft_q16p.h"
#endif

#ifdef SINGLE
void initialize_vector_s( int16_t *pSrc,
                          uint32_t fftLen)
{
  int lower = SHRT_MIN, upper = SHRT_MAX;
  for (int32_t idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {

    for (int32_t i = 0; i < 2 * N_BANKS_SINGLE; i++) {
      if (i < (int32_t) (2 * fftLen)) {
        pSrc[i + idx_fft * 2 * N_BANKS_SINGLE] = (int16_t)(i % (upper - lower + 1));
      } else {
        pSrc[i + idx_fft * 2 * N_BANKS_SINGLE] = 0;
      }
    }

  }
}
#endif

#ifdef PARALLEL
void initialize_vector_p( int16_t *pSrc,
                          int16_t *pDst,
                          uint32_t fftLen,
                          int16_t *twiddleCoef,
                          int16_t *pCoef_src,
                          int16_t *pCoef_dst)
{
  int lower = SHRT_MIN, upper = SHRT_MAX;
  for (uint32_t idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
    for (uint32_t i = 0; i < 8 * N_BANKS; i++) {
      if(i < N_FFTs_COL * (fftLen >> 1U))
        pSrc[i + idx_row * 8 * N_BANKS] = (int16_t)((int32_t) i % (upper - lower + 1));
      else
        pSrc[i + idx_row * 8 * N_BANKS] = (int16_t) 0;
      pDst[i + idx_row * 8 * N_BANKS] = (int16_t) 0;
    }
  }
  for (uint32_t i = 0; i < 8 * N_BANKS; i++) {
    pCoef_src[i] = (int16_t) 0;
    pCoef_dst[i] = (int16_t) 0;
  }
  for (uint32_t idx_col = 0; idx_col < N_FFTs_COL; idx_col++) {
    for (uint32_t ic = 0; ic < (fftLen / 4); ic++) {
      *(v2s *)&pCoef_src[2U * ic + idx_col * (fftLen >> 2U)] = *(v2s *)&twiddleCoef[2U * ic];
      *(v2s *)&pCoef_src[2U * (ic + 1 * N_BANKS) + idx_col * (fftLen >> 2U)] = *(v2s *)&twiddleCoef[2U * (ic * 2U)];
      *(v2s *)&pCoef_src[2U * (ic + 2 * N_BANKS) + idx_col * (fftLen >> 2U)] = *(v2s *)&twiddleCoef[2U * (ic * 3U)];
    }
  }
}
#endif

int volatile error __attribute__((section(".l1")));
int main() {

  uint32_t core_id = mempool_get_core_id();
  mempool_barrier_init(core_id);
  if (core_id == 0)  {

    printf("On the run...\n");
    error = 0;


    #ifdef SINGLE
    initialize_vector_s(  pSrc16,
                          N_CSAMPLES);
    #endif

    #ifdef PARALLEL
    assert(N_FFTs_COL <= MAX_COL);
    initialize_vector_p(  pSrc16,
                          pDst16,
                          N_CSAMPLES,
                          twiddleCoef_q16,
                          pCoef16_src,
                          pCoef16_dst);
    #endif

    printf("Done initialization\n");

  }
  mempool_barrier(NUM_CORES);

#ifdef SINGLE
  if(core_id == 0) {
    #if (N_CSAMPLES == 64)
    mempool_start_benchmark();
    mempool_cfft_q16s(  N_CSAMPLES,
                        pSrc16,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_64,
                        BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                        BIT_REV);
    mempool_stop_benchmark();
    #endif
    #if (N_CSAMPLES == 256)
    mempool_start_benchmark();
    mempool_cfft_q16s(  N_CSAMPLES,
                        pSrc16,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_256,
                        BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                        BIT_REV);
    mempool_stop_benchmark();
    #endif
    #if (N_CSAMPLES == 1024)
    mempool_start_benchmark();
    mempool_cfft_q16s(  N_CSAMPLES,
                        pSrc16,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_1024,
                        BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                        BIT_REV);
    mempool_stop_benchmark();
    #endif
    #if (N_CSAMPLES == 4096)
    mempool_start_benchmark();
    mempool_cfft_q16s(  N_CSAMPLES,
                        pSrc16,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_4096,
                        BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                        BIT_REV);
    mempool_stop_benchmark();
    #endif
  }
#endif

#ifdef PARALLEL
  #if (N_CSAMPLES == 64)
  if (core_id < N_FFTs_COL * (N_CSAMPLES >> 4U)) {
  mempool_start_benchmark();
  mempool_cfft_columnwrapper( pSrc16,
                              pDst16,
                              N_CSAMPLES,
                              pCoef16_src,
                              pCoef16_dst,
                              BitRevIndexTable_fixed_64,
                              BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                              BIT_REV,
                              N_CSAMPLES >> 4U);
  mempool_stop_benchmark();
  }
  #endif
  #if (N_CSAMPLES == 256)
  if (core_id < N_FFTs_COL * (N_CSAMPLES >> 4U)) {
  mempool_start_benchmark();
  mempool_cfft_columnwrapper( pSrc16,
                              pDst16,
                              N_CSAMPLES,
                              pCoef16_src,
                              pCoef16_dst,
                              BitRevIndexTable_fixed_256,
                              BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                              BIT_REV,
                              N_CSAMPLES >> 4U);
  mempool_stop_benchmark();
  }
  #endif
  #if (N_CSAMPLES == 1024)
  if (core_id < N_FFTs_COL * (N_CSAMPLES >> 4U)) {
  mempool_start_benchmark();
  mempool_cfft_columnwrapper( pSrc16,
                              pDst16,
                              N_CSAMPLES,
                              pCoef16_src,
                              pCoef16_dst,
                              BitRevIndexTable_fixed_1024,
                              BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                              BIT_REV,
                              N_CSAMPLES >> 4U);
  mempool_stop_benchmark();
  }
  #endif
  #if (N_CSAMPLES == 4096)
  mempool_start_benchmark();
  mempool_cfft_columnwrapper( pSrc16,
                              pDst16,
                              N_CSAMPLES,
                              pCoef16_src,
                              pCoef16_dst,
                              BitRevIndexTable_fixed_4096,
                              BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                              BIT_REV,
                              N_CSAMPLES >> 4U);
  mempool_stop_benchmark();
  #endif
#endif

  if (core_id == 0)  {
    printf("Done\n");
  }
  mempool_barrier(NUM_CORES);
  return error;

}
