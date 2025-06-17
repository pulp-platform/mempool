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

#include "data_cfft_radix4_f16.h"

/*
======================
Parameters and defines

PARALLEL: When defined runs parallel FFT.
FOLDED: When defined runs parallel FFT with folded inputs in memory.
FOLDED_TWIDDLES: When FOLDED is defined fold the twiddle factors in memory.
BITREVERSETABLE: When defined bitreversal idx are fetched, else they are
computed.

SCHEDULED: When defined runs multiple parallel folded-inputs FFTs.
N_FFTs_ROW: When the FFT is scheduled defines the number of FFTs run
sequentially by each core.
N_FFTs_COL: When the FFT is scheduled defines the number of FFTs run in parallel
by groups of cores.
*/

#define PARALLEL
#define BITREVERSETABLE

#define N_FFTs_ROW (1)
#define N_FFTs_COL (1)
#define MAX_COL (NUM_BANKS / (N_CSAMPLES / 4))
#if (N_FFTs_COL > MAX_COL)
#error Parallelization not supporting N_FFTs_COL > [NUM_BANKS / (N_CSAMPLES / 4)]
#endif

#include "baremetal/mempool_cfft_q16_bitreversal.h"
#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_radix4_cfft_butterfly_f16.h"
#include "baremetal/mempool_radix4_cfft_f16p.h"

#if (defined(SINGLE) || defined(PARALLEL))
__fp16 l1_pSrc[2 * N_CSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_pDst[2 * N_CSAMPLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_src[2 * N_TWIDDLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_dst[2 * N_TWIDDLES]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#endif

#if (defined(SCHEDULED) || defined(FOLDED))
__fp16 l1_pSrc[N_FFTs_ROW * 8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_pDst[N_FFTs_ROW * 8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_src[8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_dst[8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
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
                        N_TWIDDLES * sizeof(int32_t));
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
        dma_memcpy_blocking(l1_pSrc + i * 2 * N_CSAMPLES + j * (8 * NUM_BANKS),
                            l2_pSrc, N_CSAMPLES * sizeof(int32_t));
      }
    }
    dma_memcpy_blocking(l1_twiddleCoef_f16_src, l2_twiddleCoef_f16,
                        N_TWIDDLES * sizeof(int32_t));
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
      *(v2h *)&l1_twiddleCoef_f16_src[2 *
                                      (i + j * N_WORDS_COL + 1 * NUM_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2 * (i * 2U)];
      *(v2h *)&l1_twiddleCoef_f16_src[2 *
                                      (i + j * N_WORDS_COL + 2 * NUM_BANKS)] =
          *(v2h *)&l2_twiddleCoef_f16[2 * (i * 3U)];
    }
  }
  mempool_barrier(num_cores);
#endif

  if (core_id == 0) {
    printf("01: END INITIALIZATION\n");
  }
  mempool_barrier(num_cores);
#endif

  /* COMPUTATION */

#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix4_cfft_f16p(l1_pSrc, N_CSAMPLES, l1_twiddleCoef_f16_src,
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

  mempool_check_f16(pRes, l2_pRes, 2 * N_CSAMPLES, (float)TOLERANCE, 0);
  mempool_barrier(num_cores);
  return 0;
}
