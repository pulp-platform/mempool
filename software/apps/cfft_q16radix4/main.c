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
    #ifdef MEMSIZED
    for (i = core_id; i < 8 * N_BANKS; i += NUM_CORES) {
      pCoef16_src[i] = (int16_t) 0;
      pCoef16_dst[i] = (int16_t) 0;
    }
    for (uint32_t ic = core_id; ic < (N_CSAMPLES / 4); ic += NUM_CORES) {
      *(v2s *)&pCoef16_src[2U * ic] = *(v2s *)&twiddleCoef_q16[2U * ic];
      *(v2s *)&pCoef16_src[2U * (ic + 1 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (ic * 2U)];
      *(v2s *)&pCoef16_src[2U * (ic + 2 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (ic * 3U)];
    }
    #endif
    mempool_barrier(NUM_CORES);
}

int volatile error __attribute__((section(".l1")));
int main() {

    uint32_t core_id = mempool_get_core_id();
    mempool_barrier_init(core_id);

    /* SINGLE-CORE */

    #ifdef SINGLE

    initialize_vector(pSrc, pDst, N_RSAMPLES);
    if (core_id == 0)  {
        printf("On the run...\n");
        error = 0;
        mempool_start_benchmark();
        mempool_cfft_q16s(  (uint16_t) N_CSAMPLES,
                            twiddleCoef_q16,
                            BitRevIndexTable_fixed,
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

    initialize_vector(pSrc, pDst, N_RSAMPLES);
    if (core_id == 0)  {
      error = 0;
      printf("On the run...\n");
    }
    mempool_barrier(NUM_CORES);

    #if defined(TEST_64) || defined(TEST_128) || defined(TEST_256) || defined(TEST_1024) || defined(TEST_4096)
        #ifdef MEMSIZED
        if (core_id < (N_CSAMPLES / 16)) {
            #ifdef TWIDDLE_MODIFIER
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        twiddleCoef_q16,
                                        BitRevIndexTable_fixed,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_start_benchmark();
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        twiddleCoef_q16,
                                        BitRevIndexTable_fixed,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_stop_benchmark();
            #else
            mempool_start_benchmark();
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pCoef16_dst,
                                        BitRevIndexTable_fixed,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_stop_benchmark();
            mempool_start_benchmark();
            mempool_cfft_memsized_q16p( (uint16_t) N_CSAMPLES,
                                        pCoef16_src,
                                        pCoef16_dst,
                                        BitRevIndexTable_fixed,
                                        pSrc,
                                        pDst,
                                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                                        0, BIT_REV, (N_CSAMPLES / 16));
            mempool_stop_benchmark();
            #endif
        }
        #else
        mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                            twiddleCoef_q16,
                            BitRevIndexTable_fixed,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV, NUM_CORES);
        mempool_start_benchmark();
        mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                            twiddleCoef_q16,
                            BitRevIndexTable_fixed,
                            pSrc,
                            BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                            0, BIT_REV, NUM_CORES);
        mempool_stop_benchmark();
        #endif
    #else
    mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) N_CSAMPLES,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed,
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
