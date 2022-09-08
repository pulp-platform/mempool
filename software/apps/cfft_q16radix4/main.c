// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

/* Mempool runtime libraries */
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

/* CFFT mempool libraries */
#include "define.h"
#include "mempool_cfft_q16_twiddleCoef.h"
#include "mempool_cfft_q16_BitRevIndexTable.h"
#include "mempool_cfft_q16_butterfly.h"
#include "mempool_cfft_q16_bitreversal.h"

#if defined(MEMSIZED)
#include "mempool_cfft_memsized_q16p.h"
#elif defined(PARALLEL)
#include "mempool_cfft_q16p.h"
#endif
#if defined(SINGLE)
#include "mempool_cfft_q16s.h"
#endif

#ifndef MEMSIZED
int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16[3 * N_CSAMPLES / 4] __attribute__((aligned(N_BANKS), section(".l1")));
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH] __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));
#else
int16_t pSrc[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pDst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16_src[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
int16_t pCoef16_dst[8 * N_BANKS] __attribute__((aligned(8 * N_BANKS), section(".l1")));
uint16_t pRevT16[BITREVINDEXTABLE_FIXED_TABLE_LENGTH] __attribute__((aligned(N_BANKS), section(".l1")));
int volatile error __attribute__((section(".l1")));
#endif

void initialize_vector (int16_t *pSrc, int16_t *pDst, uint32_t N_el) {

    int32_t lower = SHRT_MIN, upper = SHRT_MAX;
    uint32_t core_id = mempool_get_core_id();
    uint32_t i;
    srand((unsigned) 1);
    for (i = core_id; i < 8 * N_BANKS; i += NUM_CORES) {
      if(i < N_el) {
        pSrc[i] = (int16_t)((rand() % (upper - lower + 1)) + lower);
      } else {
        pSrc[i] = (int16_t) 0;
      }
      pDst[i] = (int16_t) 0;
    }
    mempool_barrier(NUM_CORES);
}

#ifdef MEMSIZED

void initialize_l1 () {
    uint32_t core_id = mempool_get_core_id();
    uint32_t i
    for (i = core_id; i < 8 * N_BANKS; i += NUM_CORES) {
      pCoef16_src[i] = (int16_t) 0;
      pCoef16_dst[i] = (int16_t) 0;
    }
    for (i = core_id; i < (N_CSAMPLES / 4); i += NUM_CORES) {
      *(v2s *)&pCoef16_src[2U * i] = *(v2s *)&twiddleCoef_q16[2U * i];
      *(v2s *)&pCoef16_src[2U * (i + 1 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (i * 2U)];
      *(v2s *)&pCoef16_src[2U * (i + 2 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (i * 3U)];
    }
    for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += NUM_CORES) {
      *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
    }
    mempool_barrier(NUM_CORES);
}

#else

void initialize_l1 () {
    uint32_t core_id = mempool_get_core_id();
    uint32_t i;
    for (i = core_id; i < (3 * N_CSAMPLES / 4); i += NUM_CORES) {
      *(v2s *)&pCoef16[2U * i] = *(v2s *)&twiddleCoef_q16[2U * i];
    }
    for (i = core_id; i < BITREVINDEXTABLE_FIXED_TABLE_LENGTH; i += NUM_CORES) {
      *(v2s *)&pRevT16[2U * i] = *(v2s *)&BitRevIndexTable_fixed[2U * i];
    }
    mempool_barrier(NUM_CORES);
}

#endif


int main() {

    uint32_t core_id = mempool_get_core_id();
    mempool_barrier_init(core_id);

    initialize_vector(pSrc, pDst, N_RSAMPLES);
    initialize_l1 ();
    if (core_id == 0)  {
        printf("On the run...\n");
        error = 0;
    }
    mempool_barrier(NUM_CORES);

/* SINGLE-CORE */
#ifdef SINGLE

    if (core_id == 0)  {
        mempool_cfft_q16s(  (uint16_t) N_CSAMPLES,
                            pCoef16,
                            pRevT16,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV);
        mempool_start_benchmark();
        mempool_cfft_q16s(  (uint16_t) N_CSAMPLES,
                            pCoef16,
                            pRevT16,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV);
        mempool_stop_benchmark();
        printf("Done SINGLE!\n");
        #ifdef PRINT_SINGLE
        for(uint32_t i = 0; i < N_RSAMPLES; i += 2) {
          printf("{%6d; %6d} \n", pSrc[i], pSrc[i + 1]);
        }
        #endif
    }
    mempool_barrier(NUM_CORES);

#endif


/* MULTI-CORE */
#ifdef PARALLEL
#if defined(TEST_64) || defined(TEST_128) || defined(TEST_256) || defined(TEST_1024) || defined(TEST_4096)

        #ifdef MEMSIZED
        if (core_id < (N_CSAMPLES / 16)) {
        #ifdef TWIDDLE_MODIFIER
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pRevT16,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_start_benchmark();
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pRevT16,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_stop_benchmark();
            #else
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pCoef16_dst,
                                        pRevT16,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_start_benchmark();
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pCoef16_dst,
                                        pRevT16,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_stop_benchmark();
        #endif
        }
        #else
        mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                            pCoef16,
                            pRevT16,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV, NUM_CORES);
        mempool_start_benchmark();
        mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                            pCoef16,
                            pRevT16,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV, NUM_CORES);
        mempool_stop_benchmark();
        #endif

#else

    mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                        pCoef16,
                        BpRevT16,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                        pCoef16,
                        pRevT16,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

#endif

    if(core_id == 0) {
        printf("Done PARALLEL!\n");
        #ifdef PRINT_PARALLEL
        for(uint32_t i = 0; i < N_RSAMPLES; i += 2) {
            printf("{%6d; %6d} \n", pSrc[i], pSrc[i + 1]);
        }
        #endif
    }
    mempool_barrier(NUM_CORES);

#endif

    return error;
}
