// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Mempool runtime libraries */
#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

/* CFFT data libraries */
#include "data_cfft_radix4_f16.h"

/* CHOOSE ONE */
//#define PARALLEL // Parallel FFT not "memory-aware".
//#define FOLDED // Parallel FFT with "memory-aware" load/store.
#define SCHEDULED // Folded FFTs arranged in rows and cols.'''

// Bitreversal index from table.
#define BITREVERSETABLE
// Independent FFTs scheduled on one row (default 1).
#define N_FFTs_ROW 1
// Independent FFTs scheduled on columns (default 1).
#define N_FFTs_COL 1
#if (N_FFTs_COL > MAX_COL)
#error Parallelization not supporting N_FFTs_COL > [N_BANKS / (N_CSAMPLES / 4)]
#endif
// Also the twiddles have "memory-aware" load/stores.
#define FOLDED_TWIDDLES

#include "baremetal/mempool_cfft_q16_bitreversal.h"
#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_radix4_cfft_butterfly_f16.h"
#include "baremetal/mempool_radix4_cfft_f16p.h"

#if (defined(SINGLE) || defined(PARALLEL))
__fp16 l1_pSrc[2 * N_CSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_pDst[2 * N_CSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_src[2 * 3 * N_CSAMPLES / 4]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_dst[2 * 3 * N_CSAMPLES / 4]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#endif

#if (defined(SCHEDULED) || defined(FOLDED))
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
#endif

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  __fp16 *pRes = (__fp16 *)0;
  mempool_barrier_init(core_id);

  /* INITIALIZATION */

#if (defined(SINGLE) || defined(PARALLEL))
  if (core_id == 0) {
    dma_memcpy_blocking(l1_pSrc, l2_pSrc, N_CSAMPLES * sizeof(int32_t));
    dma_memcpy_blocking(l1_twiddleCoef_f16_src, l2_twiddleCoef_f16,
                        3 * (N_CSAMPLES / 4) * sizeof(int32_t));
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int16_t));
    printf("01: END INITIALIZATION\n");
  }
  mempool_barrier(num_cores);
#endif

#if (defined(SCHEDULED) || defined(FOLDED))

  if (core_id == 0) {
    for (uint32_t j = 0; j < N_FFTs_ROW; j++) {
      for (uint32_t i = 0; i < N_FFTs_COL; i++) {
        dma_memcpy_blocking(l1_pSrc + i * 2 * N_CSAMPLES + j * (8 * N_BANKS),
                            l2_pSrc, N_CSAMPLES * sizeof(int32_t));
      }
    }
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

#ifdef FOLDED_TWIDDLES
  for (uint32_t j = 0; j < N_FFTs_COL; j++) {
    uint32_t N_WORDS_COL = N_CSAMPLES >> 2;
    for (uint32_t i = core_id; i < N_WORDS_COL; i += num_cores) {
      *(v2h *)&l1_twiddleCoef_f16_src[2 * (i + j * N_WORDS_COL)] =
          *(v2h *)&l2_twiddleCoef_f16[2 * i];
      *(v2h *)&l1_twiddleCoef_f16_src[2 * (i + j * N_WORDS_COL + 1 * N_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2 * (i * 2U)];
      *(v2h *)&l1_twiddleCoef_f16_src[2 * (i + j * N_WORDS_COL + 2 * N_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2 * (i * 3U)];
    }
  }
#else
  if (core_id == 0) {
    dma_memcpy_blocking(l1_twiddleCoef_f16_src, l2_twiddleCoef_f16,
                        3 * (N_CSAMPLES / 4) * sizeof(int32_t));
  }
#endif
  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("01: END INITIALIZATION\n");
  }
  mempool_barrier(num_cores);
#endif

  /* COMPUTATION */

#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix4_cfft_f16p(l1_pSrc, N_CSAMPLES, l1_twiddleCoef_f16_src, 1,
                           num_cores);
  mempool_bitrevtable_q16p_xpulpimg((int16_t *)l1_pSrc, BITREVINDEXTABLE_LENGTH,
                                    l1_BitRevIndexTable, num_cores);
  mempool_stop_benchmark();
  pRes = l1_pSrc;
#endif

#ifdef FOLDED
  if (core_id < (N_CSAMPLES / 16)) {
    mempool_start_benchmark();
    mempool_radix4_cfft_f16p_folded(l1_pSrc, l1_pDst, N_CSAMPLES,
                                    l1_twiddleCoef_f16_src,
                                    l1_twiddleCoef_f16_dst, (N_CSAMPLES / 16));
    pRes = ((LOG2 / 2) % 2) == 0 ? l1_pSrc : l1_pDst;
    mempool_bitrevtable_q16p_xpulpimg((int16_t *)pRes, BITREVINDEXTABLE_LENGTH,
                                      l1_BitRevIndexTable, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
  }
#endif

#ifdef SCHEDULED
  uint32_t CORES_USED = (N_CSAMPLES / 4) / BANKING_FACTOR;
  if (core_id < N_FFTs_COL * CORES_USED) {
    mempool_start_benchmark();
    mempool_radix4_cfft_f16p_scheduler(
        l1_pSrc, l1_pDst, N_CSAMPLES, N_FFTs_ROW, N_FFTs_COL,
        l1_twiddleCoef_f16_src, l1_twiddleCoef_f16_dst, l1_BitRevIndexTable,
        BITREVINDEXTABLE_LENGTH, 1, CORES_USED);
    mempool_log_partial_barrier(2, core_id, N_FFTs_COL * CORES_USED);
    mempool_stop_benchmark();
  }
#ifdef BITREVERSETABLE
  pRes = ((LOG2 / 2) % 2) == 0 ? l1_pSrc : l1_pDst;
#else
  pRes = ((LOG2 / 2) % 2) == 0 ? l1_pDst : l1_pSrc;
#endif
#endif

  mempool_barrier(num_cores);
  if (core_id == 0) {
    printf("02: END COMPUTATION\n");
  }

  mempool_check_f16(pRes, l2_pRes, 2 * N_CSAMPLES, 0.05f, 0);
  mempool_barrier(num_cores);
  return 0;
}
