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

#define TEST_4096
#define LOG2 (12)
#define N_CSAMPLES (4096)
#define N_RSAMPLES (2 * N_CSAMPLES)
#define BITREVERSETABLE

/* CHOOSE ONE */
#define SINGLE
//#define PARALLEL
//#define FOLDED
//#define FOLDED_TWIDDLES
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

/* MAIN */

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  int16_t *pRes;

  initialize_vector(pSrc, pDst, N_RSAMPLES);
  initialize_l1();
  if (core_id == 0) {
    printf("On the run...\n");
    error = 0;
  }
  mempool_barrier(num_cores);

/* SINGLE-CORE */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_radix4_cfft_q16s_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16, 1);
    mempool_bitrevtable_q16s_xpulpimg(
        (uint16_t *)pSrc, BITREVINDEXTABLE_FIXED_TABLE_LENGTH, pRevT16);
    mempool_stop_benchmark();
    pRes = pSrc;
  }
  mempool_barrier(num_cores);
#endif

/* MULTI-CORE */
#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix4_cfft_q16p_xpulpimg(pSrc, (uint16_t)N_CSAMPLES, pCoef16, 1,
                                    num_cores);
  mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                    BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                    pRevT16, num_cores);
  mempool_stop_benchmark();
  pRes = pSrc;
#endif
  mempool_barrier(num_cores);

/* MULTI-CORE FOLDED */
#ifdef FOLDED
  if ((core_id < (N_CSAMPLES / 16)) && (core_id % WU_STRIDE == 0)) {
//    if (core_id == 0) {
//      set_wake_up_stride(WU_STRIDE);
//      set_wake_up_offset(0U);
//    }
#ifdef FOLDED_TWIDDLES
    mempool_start_benchmark();
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES,
                                    pCoef16_src, pCoef16_dst,
                                    (N_CSAMPLES / 16));
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
    pRes = pSrc;
#else
    mempool_start_benchmark();
    mempool_radix4_cfft_q16p_folded(pSrc, pDst, (uint16_t)N_CSAMPLES, pCoef16,
                                    (N_CSAMPLES / 16));
    mempool_bitrevtable_q16p_xpulpimg((uint16_t *)pSrc,
                                      BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                      pRevT16, (N_CSAMPLES / 16));
    mempool_stop_benchmark();
    pRes = pSrc;
#endif
    //    if (core_id == 0) {
    //      set_wake_up_stride(1U);
    //      set_wake_up_offset(0U);
    //    }
  }
  mempool_barrier(num_cores);

#endif

  if (core_id == 0) {
    printf("Done!\n");
    for (uint32_t i = 0; i < N_CSAMPLES; i++) {
      if (ABS(((int32_t)pRes[i] - (int32_t)vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, pSrc[i], i,
               vector_res[i]);
    }
  }
  mempool_barrier(num_cores);

  return error;
}
