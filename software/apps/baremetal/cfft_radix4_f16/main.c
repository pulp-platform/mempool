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
#include "data/data_cfft_radix4_f16.h"

/*
   - FOLDED:    Parallel FFT with "memory-aware" load/store scheme
   - SCHEDULED: Scheduling of multiple parallel FFTs with "memory-aware"
   load/store scheme
      - N_FFTs_COL: Independent FFTs scheduled on one row (default 1)
      - N_FFTs_ROW: Independent FFTs scheduled on columns (default 1)
      - FOLDED_TWIDDLES: Also the twiddles have "memory-aware" load/stores
*/

#define FOLDED
#define FOLDED_TWIDDLES
#define N_FFTs_ROW 1
#define N_FFTs_COL 1

#include "kernel/mempool_checks.h"
#include "kernel/mempool_radix4_cfft_butterfly_f16.h"
#include "kernel/mempool_radix4_cfft_f16p.h"
#include "kernel/mempool_radix4_cfft_q16_bitreversal.h"

__fp16 l1_pSrc[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
__fp16 l1_pDst[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_src[8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_dst[8 * N_BANKS]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  __fp16 *pRes = (__fp16 *)0;

  if (core_id == 0) {
    // Each FFT is folded over 4 memory rows
    // Each memory row is 2 * N_BANKS (real-imag) samples
    for (uint32_t j = 0; j < N_FFTs_ROW; j++) {
      dma_memcpy_blocking(l1_pSrc + j * (8 * N_BANKS), l2_pSrc,
                          (N_CSAMPLES * N_FFTs_COL) * sizeof(int32_t));
    }
    dma_memcpy_blocking(l1_pSrc, l2_pSrc, N_CSAMPLES * sizeof(int32_t));
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int16_t));
    dma_memcpy_blocking(l1_twiddleCoef_f16_src, l2_twiddleCoef_f16,
                        3 * (N_CSAMPLES / 4) * sizeof(int32_t));
  }
// Initialize the Twiddles folded
#ifdef FOLDED_TWIDDLES
  for (uint32_t j = 0; j < N_FFTs_COL; j++) {
    uint32_t N_WORDS_COL = (N_CSAMPLES / 4);
    for (uint32_t i = core_id; i < N_WORDS_COL; i += num_cores) {
      *(v2h *)&l1_twiddleCoef_f16_src[2U * (i + j * N_WORDS_COL)] =
          *(v2h *)&l2_twiddleCoef_f16[2U * i];
      *(v2h *)&l1_twiddleCoef_f16_src[2U *
                                      (i + j * N_WORDS_COL + 1 * N_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2U * (i * 2U)];
      *(v2h *)&l1_twiddleCoef_f16_src[2U *
                                      (i + j * N_WORDS_COL + 2 * N_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2U * (i * 3U)];
    }
  }
#endif
  if (core_id == 0) {
    printf("01: END INITIALIZATION\n");
  }
  mempool_barrier(num_cores);

#if (defined(FOLDED) && defined(FOLDED_TWIDDLES))
  if (core_id < (N_CSAMPLES / 16)) {
    mempool_start_benchmark();
    mempool_radix4_cfft_f16p_folded(l1_pSrc, l1_pDst, N_CSAMPLES,
                                    l1_twiddleCoef_f16_src,
                                    l1_twiddleCoef_f16_dst, (N_CSAMPLES / 16));
    pRes = ((LOG2 / 2) % 2) == 0 ? l1_pSrc : l1_pDst;
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pRes, BITREVINDEXTABLE_LENGTH,
                                      l1_BitRevIndexTable, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
  }
#endif

#ifdef SCHEDULED
  uint32_t nPE = (N_CSAMPLES / 16);
  if (core_id < N_FFTs_COL * nPE) {
    mempool_start_benchmark();
    uint32_t N_WORDS_COL = N_CSAMPLES / 4;
    uint32_t col_id = core_id / nPE;
    mempool_radix4_cfft_f16p_scheduler(
        l1_pSrc, l1_pDst, N_CSAMPLES, N_FFTs_ROW, N_FFTs_COL,
        l1_twiddleCoef_f16_src + 2 * col_id * N_WORDS_COL,
        l1_twiddleCoef_f16_dst + 2 * col_id * N_WORDS_COL, l1_BitRevIndexTable,
        BITREVINDEXTABLE_LENGTH, 1, nPE);
    pRes = l1_pDst;
    mempool_log_partial_barrier(2, core_id, N_FFTs_COL * nPE);
    mempool_stop_benchmark();
  }
#endif

  mempool_barrier(num_cores);
  if (core_id == 0) {
    printf("02: END COMPUTATION\n");
  }
  mempool_check_f16(pRes, l2_pRes, 2 * N_CSAMPLES, 0.5, 0);
  mempool_barrier(num_cores);
  return 0;
}
