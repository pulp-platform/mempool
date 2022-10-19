// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Mempool runtime libraries */
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

/* CFFT mempool libraries */
#include "define.h"
#include "mempool_cfft_q16_BitRevIndexTable.h"
#include "mempool_cfft_q16_twiddleCoef.h"

#ifdef SINGLE
#include "mempool_cfft_q16s.h"
#endif
#ifdef PARALLEL
#include "mempool_cfft_q16p.h"
#endif

#if defined(SINGLE)

int volatile error __attribute__((section(".l1")));

#define N_BANKS_SINGLE (N_BANKS * ((N_CSAMPLES + N_BANKS - 1) / N_BANKS))
int16_t pSrc16[N_FFTs * 2 * N_BANKS_SINGLE]
    __attribute__((aligned(N_FFTs * 2 * N_BANKS_SINGLE), section(".l1")));
int16_t pCoef16[3 * N_CSAMPLES / 4]
    __attribute__((aligned(N_BANKS), section(".l1")));
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
void initialize_vector_s(int16_t *pSrc, uint32_t fftLen) {
  int32_t lower = SHRT_MIN, upper = SHRT_MAX;
  uint32_t idx_fft, i;
  uint32_t core_id = mempool_get_core_id();
  for (idx_fft = 0; idx_fft < N_FFTs; idx_fft++) {
    for (i = core_id; i < 2 * N_BANKS_SINGLE; i += NUM_CORES) {
      if (i < (2 * fftLen)) {
        pSrc[i + idx_fft * 2 * N_BANKS_SINGLE] =
            (int16_t)((int16_t)i % (upper - lower + 1));
      } else {
        pSrc[i + idx_fft * 2 * N_BANKS_SINGLE] = 0;
      }
    }
  }
  for (i = core_id; i < (3 * N_CSAMPLES / 4); i += NUM_CORES) {
    *(v2s *)&pCoef16[2U * i] = *(v2s *)&twiddleCoef_q16[2U * i];
  }
  for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += NUM_CORES) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
  }
  mempool_barrier(NUM_CORES);
}

#endif

#if defined(PARALLEL)

int16_t pSrc16[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
int16_t pDst16[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
int16_t pCoef16_src[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16_dst[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
void initialize_vector_p(int16_t *pSrc, int16_t *pDst, uint32_t fftLen,
                         int16_t *twiddleCoef, int16_t *pCoef_src,
                         int16_t *pCoef_dst) {

  int32_t lower = SHRT_MIN, upper = SHRT_MAX;
  uint32_t idx_row, idx_col;
  uint32_t i, ic;
  uint32_t core_id = mempool_get_core_id();
  for (idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
    for (i = core_id; i < 8 * N_BANKS; i += NUM_CORES) {
      if (i < N_FFTs_COL * (fftLen >> 1U))
        pSrc[i + idx_row * 8 * N_BANKS] =
            (int16_t)((int32_t)i % (upper - lower + 1));
      else
        pSrc[i + idx_row * 8 * N_BANKS] = (int16_t)0;
      pDst[i + idx_row * 8 * N_BANKS] = (int16_t)0;
    }
  }
  for (i = core_id; i < 8 * N_BANKS; i += NUM_CORES) {
    pCoef_src[i] = (int16_t)0;
    pCoef_dst[i] = (int16_t)0;
  }
  for (idx_col = 0; idx_col < N_FFTs_COL; idx_col++) {
    for (ic = core_id; ic < (fftLen / 4); ic += NUM_CORES) {
      *(v2s *)&pCoef_src[2U * ic + idx_col * (fftLen >> 2U)] =
          *(v2s *)&twiddleCoef[2U * ic];
      *(v2s *)&pCoef_src[2U * (ic + 1 * N_BANKS) + idx_col * (fftLen >> 2U)] =
          *(v2s *)&twiddleCoef[2U * (ic * 2U)];
      *(v2s *)&pCoef_src[2U * (ic + 2 * N_BANKS) + idx_col * (fftLen >> 2U)] =
          *(v2s *)&twiddleCoef[2U * (ic * 3U)];
    }
  }
#ifdef BITREVERSALTABLE
  for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += NUM_CORES) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
  }
#endif
  mempool_barrier(NUM_CORES);
}

#endif

int main() {

  uint32_t core_id = mempool_get_core_id();
  mempool_barrier_init(core_id);
  if (core_id == 0) {
    printf("On the run...\n");
    error = 0;
  }
  mempool_barrier(NUM_CORES);

#ifdef SINGLE

  /* Initialization */
  initialize_vector_s(pSrc16, N_CSAMPLES);
  if (core_id == 0)
    printf("Done initialization\n");
  mempool_barrier(NUM_CORES);

  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cfft_q16s(N_CSAMPLES, pSrc16, pCoef16, pRevT16,
                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH, BIT_REV);
    mempool_stop_benchmark();
  }
#endif

#ifdef PARALLEL

  assert(N_FFTs_COL <= MAX_COL);
  initialize_vector_p(pSrc16, pDst16, N_CSAMPLES, twiddleCoef_q16, pCoef16_src,
                      pCoef16_dst);
  if (core_id == 0)
    printf("Done initialization\n");
  mempool_barrier(NUM_CORES);

  if (core_id < N_FFTs_COL * (N_CSAMPLES >> 4U)) {
    mempool_start_benchmark();
    mempool_cfft_columnwrapper(
        pSrc16, pDst16, N_CSAMPLES, pCoef16_src, pCoef16_dst, pRevT16,
        BITREVINDEXTABLE_FIXED_TABLE_LENGTH, BIT_REV, N_CSAMPLES >> 4U);
    mempool_stop_benchmark();
  }
#endif
  mempool_barrier(NUM_CORES);

  if (core_id == 0) {
    printf("Done\n");
  }
  mempool_barrier(NUM_CORES);
  return error;
}
