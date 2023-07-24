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

/* CFFT data libraries */
#include "data/data_cfft_radix4_q16.h"

/*
  CHOOSE ONE
   - SINGLE:    Single core FFT
   - PARALLEL:  Parallel FFT not "memory-aware"
   - FOLDED:    Parallel FFT with "memory-aware" load/store scheme
   - SCHEDULED: Scheduling of multiple parallel FFTs with "memory-aware"
  load/store scheme
      - N_FFTs_COL: Independent FFTs scheduled on one row (default 1)
      - N_FFTs_ROW: Independent FFTs scheduled on columns (default 1)
      (OPTIONALLY ENABLE)
      - FOLDED_TWIDDLES: Also the twiddles have "memory-aware" load/stores
      - BITREVERSETABLE: The bitreversal indeces are loaded from a table
      - ASM:             Use asm_volatile statements
*/

#define FOLDED
#define FOLDED_TWIDDLES
#define BITREVERSETABLE
#define ASM // Use asm_volatile statements

#define WU_STRIDE (1)
#define STEP (4 * WU_STRIDE)
#if !(defined(N_FFTs_ROW) && defined(N_FFTs_COL))
#define N_FFTs_ROW 2
#define N_FFTs_COL 1
#endif

#define ABS(x) (((x) < 0) ? (-x) : (x))
#include "kernel/mempool_radix4_cfft_butterfly_q16.h"
#include "kernel/mempool_radix4_cfft_q16_bitreversal.h"
#include "kernel/mempool_radix4_cfft_q16p.h"
#include "kernel/mempool_radix4_cfft_q16s.h"

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

///////////////////////////////////////////////////////////////////////////////////////////////////
/* INITIALIZATION FUNCTIONS*/

void initialize_l1() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize the inputs and results from the data.h file
  for (uint32_t j = 0; j < N_FFTs_ROW; j++) {
    for (uint32_t i = core_id; i < (8 * N_BANKS); i += num_cores) {
      if (i < N_RSAMPLES * N_FFTs_COL) {
        pSrc[j * (8 * N_BANKS) + i] = (int16_t)vector_inp[i % N_RSAMPLES];
      } else {
        pSrc[j * (8 * N_BANKS) + i] = (int16_t)0;
      }
      pDst[j * (8 * N_BANKS) + i] = (int16_t)0;
    }
  }
  // Initialize the Bitreversal table
  for (uint32_t i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH;
       i += num_cores) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable[2U * i];
  }
  mempool_barrier(num_cores);

// Initialize the Twiddles
#ifdef FOLDED_TWIDDLES
  for (uint32_t i = core_id; i < 8 * N_BANKS; i += num_cores) {
    pCoef16_src[i] = (int16_t)0;
    pCoef16_dst[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
  for (uint32_t j = 0; j < N_FFTs_COL; j++) {
    uint32_t N_WORDS_COL = (N_CSAMPLES / 4);
    for (uint32_t i = core_id; i < N_WORDS_COL; i += num_cores) {
      *(v2s *)&pCoef16_src[2U * (i + j * (N_CSAMPLES / 4))] =
          *(v2s *)&twiddleCoef_q16[2U * i];
      *(v2s *)&pCoef16_src[2U * (i + j * (N_CSAMPLES / 4) + 1 * N_BANKS)] =
          *(v2s *)&twiddleCoef_q16[2U * (i * 2U)];
      *(v2s *)&pCoef16_src[2U * (i + j * (N_CSAMPLES / 4) + 2 * N_BANKS)] =
          *(v2s *)&twiddleCoef_q16[2U * (i * 3U)];
    }
  }
#else
  for (uint32_t i = core_id; i < 6 * (N_CSAMPLES / 4); i += num_cores) {
    pCoef16_src[i] = twiddleCoef_q16[i];
  }
#endif
  mempool_barrier(num_cores);
}

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
  int16_t *pRes; // Result pointer
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_radix4_cfft_q16s_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16_src,
                                      1);
    mempool_bitrevtable_q16s_xpulpimg(
        (uint16_t *)pSrc, BITREVINDEXTABLE_FIXED_TABLE_LENGTH, pRevT16);
    pRes = pSrc;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE */
#ifdef PARALLEL
  int16_t *pRes; // Result pointer
  mempool_start_benchmark();
  mempool_radix4_cfft_q16p_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16_src, 1,
                                    num_cores);
  mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                    BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                    pRevT16, num_cores);
  pRes = pSrc;
  mempool_stop_benchmark();
#endif
  mempool_barrier(num_cores);

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE FOLDED */
#ifdef FOLDED
  int16_t *pRes; // Result pointer
  if ((core_id < (N_CSAMPLES / 16)) && (core_id % WU_STRIDE == 0)) {
    mempool_start_benchmark();
#ifdef FOLDED_TWIDDLES
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES,
                                    pCoef16_src, pCoef16_dst,
                                    (N_CSAMPLES / 16));
#else
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES,
                                    pCoef16_src, (N_CSAMPLES / 16));
#endif
    pRes = (LOG2 % 2) == 0 ? pDst : pSrc;
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pRes,
                                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* CHECK */
#if defined(SINGLE) || defined(PARALLEL) || defined(FOLDED)
  if (core_id == 0) {
    printf("Done!\n");
    for (uint32_t i = 0; i < N_RSAMPLES; i++) {
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
