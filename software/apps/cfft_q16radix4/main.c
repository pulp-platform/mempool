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
#include "data_cfftq16.h"
#include "define.h"
#include "mempool_cfft_q16_BitRevIndexTable.h"
#include "mempool_cfft_q16_twiddleCoef.h"

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
/* SINGLE-CORE */

#if defined(SINGLE)

#include "mempool_cfft_q16_bitreversal.h"

#include "mempool_cfft_q16s_butterfly.h"

#include "mempool_cfft_q16s.h"

int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16[6 * N_CSAMPLES / 4];
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));

#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE */

#if defined(PARALLEL)

#include "mempool_cfft_q16_bitreversal.h"

#include "mempool_cfft_q16p_butterfly.h"

#include "mempool_cfft_q16p.h"

int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16[6 * N_CSAMPLES / 4];
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH]
    __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));

#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
/* MULTI-CORE FOLDED*/

#if defined(FOLDED)

#include "mempool_cfft_q16_bitreversal.h"

#include "mempool_cfft_q16p_butterfly_folded.h"

#include "mempool_cfft_q16p_folded.h"

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
///////////////////////////////////////////////////////////////////////////////////////////////////
/* INITIALIZATION FUNCTIONS*/

void initialize_vector(int16_t *pSrc, int16_t *pDst, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i;
  for (i = core_id; i < 8 * N_BANKS; i += num_cores) {
    if (i < N_el) {
      pSrc[i] = (int16_t)vector_inp[i];
    } else {
      pSrc[i] = (int16_t)0;
    }
    pDst[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
}

#ifdef FOLDED_TWIDDLES

void initialize_l1() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i = 0;
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
#ifdef BITREVERSETABLE
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
  for (i = core_id; i < (6 * N_CSAMPLES / 4); i += num_cores) {
    pCoef16[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
  for (i = core_id; i < 6 * (N_CSAMPLES / 4); i += num_cores) {
    pCoef16[i] = twiddleCoef_q16[i];
  }
#ifdef BITREVERSETABLE
  for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += num_cores) {
    *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
  }
#endif
  mempool_barrier(num_cores);
}

#endif

///////////////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////////////
/* MAIN */

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize_vector(pSrc, pDst, N_RSAMPLES);
  initialize_l1();
  if (core_id == 0) {
    printf("On the run...\n");
    error = 0;
  }
  mempool_barrier(num_cores);

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* SINGLE-CORE */

#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cfft_q16s((uint16_t)N_CSAMPLES, pCoef16, pRevT16, pSrc,
                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, BIT_REV);
    mempool_stop_benchmark();
#ifdef PRINT_SINGLE
    printf("Done SINGLE!\n");
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pSrc[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pSrc[i], i,
               vector_res[i]);
    }
#endif
  }
  mempool_barrier(num_cores);
#endif

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* MULTI-CORE */

#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_cfft_q16p((uint16_t)N_CSAMPLES, pCoef16, pRevT16, pSrc,
                    BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, BIT_REV, num_cores);
  mempool_stop_benchmark();
#endif
  if (core_id == 0) {
#ifdef PRINT_PARALLEL
    printf("Done PARALLEL!\n");
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pSrc[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pSrc[i], i,
               vector_res[i]);
    }
#endif
  }
  mempool_barrier(num_cores);

  ///////////////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////////////
  /* MULTI-CORE FOLDED */

#ifdef FOLDED
  int16_t *pIn;
  int16_t *pRes;
  pIn = (int16_t *)pSrc;
  pRes = (int16_t *)pDst;
  if ((core_id < (N_CSAMPLES / 16)) && (core_id % WU_STRIDE == 0)) {

    //    if (core_id == 0) {
    //      set_wake_up_stride(WU_STRIDE);
    //      set_wake_up_offset(0U);
    //    }

#ifdef FOLDED_TWIDDLES
    mempool_start_benchmark();
    pRes = mempool_cfft_q16p_folded(
        (uint16_t)N_CSAMPLES, pCoef16_src, pCoef16_dst, pRevT16, pIn, pRes,
        BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, BIT_REV, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
#else
    mempool_start_benchmark();
    pRes = mempool_cfft_q16p_folded((uint16_t)N_CSAMPLES, pCoef16, pRevT16, pIn,
                                    pRes, BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                    0, BIT_REV, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
#endif

    //    if (core_id == 0) {
    //      set_wake_up_stride(1U);
    //      set_wake_up_offset(0U);
    //    }
  }
  mempool_barrier(num_cores);
#endif

  if (core_id == 0) {
#ifdef PRINT_FOLDED
    printf("Done PARALLEL!\n");
#ifndef BITREVERSETABLE
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pRes[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pSrc[i], i,
               vector_res[i]);
    }
#else
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pRes[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pDst[i], i,
               vector_res[i]);
    }
#endif
#endif
  }
  mempool_barrier(num_cores);

  return error;
}
