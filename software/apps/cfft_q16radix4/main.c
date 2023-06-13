// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

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

#define TEST_256
#define LOG2 (12)
#define N_CSAMPLES (256)
#define N_RSAMPLES (2 * N_CSAMPLES)
//#define BITREVERSETABLE

#define N_FFTs_ROW 2
#define N_FFTs_COL 1
#define MAX_COL (N_BANKS / (N_CSAMPLES / 4))

dump(reg1, 1);

/* CHOOSE ONE */
//#define SINGLE
#define PARALLEL
//#define FOLDED
//#define FOLDED_TWIDDLES
//#define SCHEDULED
#define ASM // Use asm_volatile statements

#define N_BANKS (1024)
#define N_TWIDDLES (3 * N_CSAMPLES / 4)
#define WU_STRIDE (1)
#define STEP (4 * WU_STRIDE)

#define ABS(x) (((x) < 0) ? (-x) : (x))

/* CFFT data libraries */
#include "data_cfftq16.h"
#include "tables/mempool_radix4_cfft_q16_BitRevIndexTable.h"
#include "tables/mempool_radix4_cfft_q16_twiddleCoef.h"

#include "kernel/mempool_radix4_cfft_butterfly_q16.h"
#include "kernel/mempool_radix4_cfft_q16_bitreversal.h"
#include "kernel/mempool_radix4_cfft_q16p.h"
#include "kernel/mempool_radix4_cfft_q16s.h"

///////////////////////////////////////////////////////////////////////////////////////////////////
/* SINGLE-CORE */

#if defined(SINGLE)
int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16[6 * N_CSAMPLES / 4];
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE */

#if defined(PARALLEL)
int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16[6 * N_CSAMPLES / 4];
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE FOLDED*/

#if defined(FOLDED)
int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
#ifdef FOLDED_TWIDDLES
int16_t pCoef16_src[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16_dst[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
#else
int16_t pCoef16[6 * N_CSAMPLES / 4];
#endif
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE SCHEDULED */

#if defined(SCHEDULED)

int16_t pSrc[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
int16_t pDst[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
int16_t pCoef16_src[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16_dst[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* INITIALIZATION FUNCTIONS*/

#ifdef SCHEDULED

void initialize_l1() {
  int32_t lower = -1000, upper = 1000;
  uint32_t idx_row, idx_col;
  uint32_t i, ic;
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for (idx_row = 0; idx_row < N_FFTs_ROW; idx_row++) {
    for (i = core_id; i < 8 * N_BANKS; i += num_cores) {
      if (i < N_FFTs_COL * (N_CSAMPLES >> 1U))
        pSrc[i + idx_row * 8 * N_BANKS] =
            (int16_t)((int32_t)i % (upper - lower + 1));
      else
        pSrc[i + idx_row * 8 * N_BANKS] = (int16_t)0;
      pDst[i + idx_row * 8 * N_BANKS] = (int16_t)0;
    }
  }
  for (i = core_id; i < 8 * N_BANKS; i += num_cores) {
    pCoef16_src[i] = (int16_t)0;
    pCoef16_dst[i] = (int16_t)0;
  }
  for (idx_col = 0; idx_col < N_FFTs_COL; idx_col++) {
    for (ic = core_id; ic < (N_CSAMPLES / 4); ic += num_cores) {
      *(v2s *)&pCoef16_src[2U * ic + idx_col * (N_CSAMPLES >> 2U)] =
          *(v2s *)&twiddleCoef_q16[2U * ic];
      *(v2s *)&pCoef16_src[2U * (ic + 1 * N_BANKS) +
                           idx_col * (N_CSAMPLES >> 2U)] =
          *(v2s *)&twiddleCoef_q16[2U * (ic * 2U)];
      *(v2s *)&pCoef16_src[2U * (ic + 2 * N_BANKS) +
                           idx_col * (N_CSAMPLES >> 2U)] =
          *(v2s *)&twiddleCoef_q16[2U * (ic * 3U)];
    }
  }
#ifdef BITREVERSALTABLE
  for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += num_cores) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
  }
#endif
  mempool_barrier(num_cores);
}

#else

void initialize_l1() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i = 0;
  // Initialize the inputs and results from the data.h file
  for (i = core_id; i < 8 * N_BANKS; i += num_cores) {
    if (i < N_RSAMPLES) {
      pSrc[i] = (int16_t)vector_inp[i];
    } else {
      pSrc[i] = (int16_t)0;
    }
    pDst[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
#ifdef FOLDED_TWIDDLES
  // Initialize the Twiddles
  for (i = core_id; i < 8 * N_BANKS; i += num_cores) {
    pCoef16_src[i] = (int16_t)0;
    pCoef16_dst[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
  for (i = core_id; i < (N_CSAMPLES / 4); i += num_cores) {
    *(v2s *)&pCoef16_src[2U * i] = *(v2s *)&twiddleCoef_q16[2U * i];
    *(v2s *)&pCoef16_src[2U * (i + 1 * N_BANKS)] =
        *(v2s *)&twiddleCoef_q16[2U * (i * 2U)];
    *(v2s *)&pCoef16_src[2U * (i + 2 * N_BANKS)] =
        *(v2s *)&twiddleCoef_q16[2U * (i * 3U)];
  }
#else
  // Initialize the Twiddles
  for (i = core_id; i < 6 * (N_CSAMPLES / 4); i += num_cores) {
    pCoef16[i] = twiddleCoef_q16[i];
  }
#endif
#ifdef BITREVERSETABLE
  // Initialize the Bitreversal table
  for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += num_cores) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
  }
#endif
  mempool_barrier(num_cores);
}

#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MAIN */
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize_l1();
  if (core_id == 0) {
    printf("On the run...\n");
  }
  mempool_barrier(num_cores);

///////////////////////////////////////////////////////////////////////////////////////////////////
/* SINGLE-CORE */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_radix4_cfft_q16s_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16, 1);
    mempool_bitrevtable_q16s_xpulpimg(
        (uint16_t *)pSrc, BITREVINDEXTABLE_FIXED_TABLE_LENGTH, pRevT16);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE */
#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix4_cfft_q16p_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16, 1,
                                    num_cores);
  mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                    BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                    pRevT16, num_cores);
  mempool_stop_benchmark();
#endif
  mempool_barrier(num_cores);

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE FOLDED */
#ifdef FOLDED
  if ((core_id < (N_CSAMPLES / 16)) && (core_id % WU_STRIDE == 0)) {
#ifdef FOLDED_TWIDDLES
    mempool_start_benchmark();
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES,
                                    pCoef16_src, pCoef16_dst,
                                    (N_CSAMPLES / 16));
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
#else
    mempool_start_benchmark();
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES, pCoef16,
                                    (N_CSAMPLES / 16));
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
#endif
  }
  mempool_barrier(num_cores);
#endif

#if defined(SINGLE) || defined(PARALLEL) || defined(FOLDED)
  if (core_id == 0) {
    printf("Done!\n");
    int16_t *pRes = pSrc;
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pRes[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pSrc[i], i,
               vector_res[i]);
    }
  }
  mempool_barrier(num_cores);
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE SCHEDULED */
#ifdef SCHEDULED
  if (core_id < N_FFTs_COL * (N_CSAMPLES >> 4U)) {
    mempool_start_benchmark();
    uint32_t col_fftLen = N_CSAMPLES >> 2U;
    uint32_t col_id = core_id / (N_CSAMPLES >> 4U);
    if (col_id < N_FFTs_COL) {
      mempool_radix4_cfft_q16p_scheduler(
          col_id, pSrc + 2 * col_id * col_fftLen,
          pDst + 2 * col_id * col_fftLen, N_CSAMPLES,
          pCoef16_src + 2 * col_id * col_fftLen,
          pCoef16_dst + 2 * col_id * col_fftLen, pRevT16,
          BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 1, N_CSAMPLES >> 4U);
    }
    mempool_log_barrier(2, core_id);
    mempool_stop_benchmark();
  }
#endif
  mempool_barrier(num_cores);

  return 0;
}
