// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Mempool runtime libraries */
#include "dma.h"
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

#define SCHEDULED
#define FOLDED_TWIDDLES
#define BITREVERSETABLE
#define ASM // Use asm_volatile statements

#if !(defined(N_FFT_ROW) && defined(N_FFTs_COL))
#define N_FFTs_ROW 2
#define N_FFTs_COL 2
#endif

#define ABS(x) (((x) < 0) ? (-x) : (x))
#include "kernel/mempool_radix4_cfft_butterfly_q16.h"
#include "kernel/mempool_radix4_cfft_q16_bitreversal.h"
#include "kernel/mempool_radix4_cfft_q16p.h"
#include "kernel/mempool_radix4_cfft_q16s.h"

int16_t l1_pSrc[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
int16_t l1_pDst[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
int16_t l1_twiddleCoef_q16_src[8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
int16_t l1_twiddleCoef_q16_dst[8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MAIN */
int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* INITIALIZATION */
  if (core_id == 0) {
    // Each FFT is folded over 4 memory rows
    // Each memory row is 2 * N_BANKS samples
    for (uint32_t j = 0; j < N_FFTs_ROW; j++) {
      dma_memcpy_blocking(l1_pSrc + j * (8 * N_BANKS), l2_pSrc,
                          (N_RSAMPLES * N_FFTs_COL) * sizeof(int32_t));
    }
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int32_t));
    dma_memcpy_blocking(l1_twiddleCoef_q16_src, l2_twiddleCoef_q16,
                        3 * (N_CSAMPLES / 4) * sizeof(int32_t));
  }
  // Initialize the Twiddles folded
#ifdef FOLDED_TWIDDLES
  for (uint32_t j = 0; j < N_FFTs_COL; j++) {
    uint32_t N_WORDS_COL = (N_CSAMPLES / 4);
    for (uint32_t i = core_id; i < N_WORDS_COL; i += num_cores) {
      *(v2s *)&l1_twiddleCoef_q16_src[2U * (i + j * (N_CSAMPLES / 4))] =
          *(v2s *)&l2_twiddleCoef_q16[2U * i];
      *(v2s *)&l1_twiddleCoef_q16_src[2U * (i + j * (N_CSAMPLES / 4) +
                                            1 * N_BANKS)] =
          *(v2s *)&l2_twiddleCoef_q16[2U * (i * 2U)];
      *(v2s *)&l1_twiddleCoef_q16_src[2U * (i + j * (N_CSAMPLES / 4) +
                                            2 * N_BANKS)] =
          *(v2s *)&l2_twiddleCoef_q16[2U * (i * 3U)];
    }
  }
#endif
  mempool_barrier(num_cores);

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
    mempool_radix4_cfft_q16s_xpulpimg(l1_pSrc, (uint16_t)N_CSAMPLES,
                                      l1_twiddleCoef_q16_src, 1);
    mempool_bitrevtable_q16s_xpulpimg(
        (uint16_t *)l1_pSrc, BITREVINDEXTABLE_LENGTH, l1_BitRevIndexTable);
    pRes = l1_pSrc;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE */
#ifdef PARALLEL
  int16_t *pRes; // Result pointer
  mempool_start_benchmark();
  mempool_radix4_cfft_q16p_xpulpimg(l1_pSrc, (uint16_t)N_CSAMPLES,
                                    l1_twiddleCoef_q16_src, 1, num_cores);
  mempool_bitrevtable_q16p_xpulpimg((uint16_t *)l1_pSrc,
                                    BITREVINDEXTABLE_LENGTH,
                                    l1_BitRevIndexTable, num_cores);
  pRes = l1_pSrc;
  mempool_stop_benchmark();
#endif
  mempool_barrier(num_cores);

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE FOLDED */
#ifdef FOLDED
  int16_t *pRes; // Result pointer
  if (core_id < (N_CSAMPLES / 16)) {
    mempool_start_benchmark();
#ifdef FOLDED_TWIDDLES
    mempool_radix4_cfft_q16p_folded(l1_pSrc, l1_pDst, (uint16_t)N_CSAMPLES,
                                    l1_twiddleCoef_q16_src,
                                    l1_twiddleCoef_q16_dst, (N_CSAMPLES / 16));
#else
    mempool_radix4_cfft_q16p_folded(l1_pSrc, l1_pDst, (uint16_t)N_CSAMPLES,
                                    l1_twiddleCoef_q16_src, (N_CSAMPLES / 16));
#endif
    pRes = ((LOG2 / 2) % 2) == 0 ? l1_pSrc : l1_pDst;
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pRes, BITREVINDEXTABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
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
    mempool_radix4_cfft_q16p_scheduler(
        l1_pSrc, l1_pDst, N_CSAMPLES,
        l1_twiddleCoef_q16_src + 2 * col_id * col_fftLen,
        l1_twiddleCoef_q16_dst + 2 * col_id * col_fftLen, l1_BitRevIndexTable,
        BITREVINDEXTABLE_LENGTH, 1, N_CSAMPLES >> 4U);
    mempool_log_partial_barrier(2, core_id, N_CSAMPLES >> 4U);
    mempool_stop_benchmark();
  }
#endif
  mempool_barrier(num_cores);

///////////////////////////////////////////////////////////////////////////////////////////////////
/* CHECK */
#if defined(SINGLE) || defined(PARALLEL) || defined(FOLDED)
  if (core_id == 0) {
    printf("Done!\n");
    for (uint32_t i = 0; i < N_RSAMPLES; i++) {
      if (ABS(((int32_t)pRes[i] - (int32_t)l2_pRes[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pRes[i], i,
               l2_pRes[i]);
    }
  }
  mempool_barrier(num_cores);
#endif

  return 0;
}
