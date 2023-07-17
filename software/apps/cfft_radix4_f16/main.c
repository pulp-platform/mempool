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

#define SCHEDULED
#define FOLDED_TWIDDLES
#define BITREVERSETABLE

#define WU_STRIDE (1)
#define STEP (4 * WU_STRIDE)
#ifndef N_FFTs_ROW
#define N_FFTs_ROW 1
#endif
#ifndef N_FFTs_COL
#define N_FFTs_COL 4
#endif

#include "data/data_cfft_radix4_f16.h"
#include "kernel/mempool_cfft_radix4_butterfly_f16.h"
#include "kernel/mempool_cfft_radix4_f16p.h"
#include "kernel/mempool_cfft_radix4_q16_bitreversal.h"

__fp16 l1_pSrc[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
__fp16 l1_pDst[N_FFTs_ROW * 8 * N_BANKS]
    __attribute__((aligned(N_FFTs_ROW * 8 * N_BANKS), section(".l1")));
__fp16 l1_pCoef_src[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
__fp16 l1_pCoef_dst[8 * N_BANKS]
    __attribute__((aligned(8 * N_BANKS), section(".l1")));
uint16_t l1_pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
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
        l1_pSrc[j * (8 * N_BANKS) + i] = (__fp16)pSrc[i % N_RSAMPLES];
      } else {
        l1_pSrc[j * (8 * N_BANKS) + i] = (__fp16)0.0f;
      }
      l1_pDst[j * (8 * N_BANKS) + i] = (__fp16)0.0f;
    }
  }
  // Initialize the Bitreversal table
  for (uint32_t i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH;
       i += num_cores) {
    *(v2h *)&l1_pRevT16[2U * i] = *(v2h *)&BitRevIndexTable[2U * i];
  }
  mempool_barrier(num_cores);

// Initialize the Twiddles
#ifdef FOLDED_TWIDDLES
  for (uint32_t i = core_id; i < 8 * N_BANKS; i += num_cores) {
    l1_pCoef_src[i] = (__fp16)0.0f;
    l1_pCoef_dst[i] = (__fp16)0.0f;
  }
  mempool_barrier(num_cores);
  for (uint32_t j = 0; j < N_FFTs_COL; j++) {
    uint32_t N_WORDS_COL = (N_CSAMPLES / 4);
    for (uint32_t i = core_id; i < N_WORDS_COL; i += num_cores) {
      *(v2h *)&l1_pCoef_src[2U * (i + j * (N_CSAMPLES / 4))] =
          *(v2h *)&pTwi[2U * i];
      *(v2h *)&l1_pCoef_src[2U * (i + j * (N_CSAMPLES / 4) + 1 * N_BANKS)] =
          *(v2h *)&pTwi[2U * (i * 2U)];
      *(v2h *)&l1_pCoef_src[2U * (i + j * (N_CSAMPLES / 4) + 2 * N_BANKS)] =
          *(v2h *)&pTwi[2U * (i * 3U)];
    }
  }
#else
  for (uint32_t i = core_id; i < 6 * (N_CSAMPLES / 4); i += num_cores) {
    l1_pCoef_src[i] = pTwi[i];
  }
#endif
  mempool_barrier(num_cores);
}

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MAIN */
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t cores_fft = N_CSAMPLES / 16; // Each core gets 4 elements
  mempool_barrier_init(core_id);

  initialize_l1();
  if (core_id == 0) {
    printf("On the run...\n");
  }
  mempool_barrier(num_cores);

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* MULTI-CORE FOLDED */
#ifdef FOLDED
  if (core_id < cores_fft) {
    mempool_start_benchmark();
#ifdef FOLDED_TWIDDLES
    mempool_radix4_cfft_q16p_folded(l1_pSrc, l1_pDst, N_CSAMPLES, l1_pCoef_src,
                                    l1_pCoef_dst, cores_fft);
#else
    mempool_radix4_cfft_q16p_folded(l1_pSrc, l1_pDst, N_CSAMPLES, l1_pCoef_src,
                                    cores_fft);
#endif
    mempool_bitrev_q16p_xpulpimg((uint16_t *)l1_pDst, (uint16_t *)l1_pSrc,
                                 N_CSAMPLES, cores_fft);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* CHECK */
  if (core_id == 0) {
    printf("Done!\n");
    for (uint32_t i = 0; i < 2 * N_CSAMPLES; i++) {
      __fp16 exp = pDst[i];
      __fp16 res = l1_pDst[i];
      __fp16 dif;
      float tol = (__fp16)0.05f;
      float dif_f32;
      asm volatile("fsub.h %[dif], %[res], %[exp];"
                   "fcvt.h.s %[dif_f32], %[dif];"
                   : [dif] "+&r"(dif), [dif_f32] "+&r"(dif_f32)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      if ((dif_f32 > tol) || (dif_f32 < (-tol))) {
        printf("%d %x %x\n", i, *(int32_t *)&exp, *(int32_t *)&res);
      }
    }
  }
  mempool_barrier(num_cores);
#endif

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* MULTI-CORE SCHEDULED */
#ifdef SCHEDULED
  if (core_id < N_FFTs_COL * cores_fft) {
    mempool_start_benchmark();
    uint32_t col_fftLen = N_CSAMPLES / 4;
    uint32_t col_id = core_id / cores_fft;
    // Distribute FFTs over columns
    if (col_id < N_FFTs_COL) {
      mempool_radix4_cfft_q16p_scheduler(
          col_id, l1_pSrc, l1_pDst, N_CSAMPLES,
          l1_pCoef_src + 2 * col_id * col_fftLen,
          l1_pCoef_dst + 2 * col_id * col_fftLen, l1_pRevT16,
          BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, cores_fft);
    }
    mempool_log_partial_barrier(2, core_id, N_FFTs_COL * cores_fft);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

  return 0;
}
