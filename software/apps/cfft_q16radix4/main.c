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

/* CFFT mempool libraries */
#include "define.h"
#include "xpulp/builtins_v2.h"
#include "mempool_cfft_q16s.h"
#include "mempool_cfft_q16p.h"
#include "mempool_cfft_memsized_q16p.h"
#include "mempool_cfft_q16_twiddleCoef.h"
#include "mempool_cfft_q16_BitRevIndexTable.h"

void initialize_vector (int16_t *pSrc, int16_t *pDst, uint32_t N_el) {
    int lower = SHRT_MIN, upper = SHRT_MAX;
    srand((unsigned) 1);
    for (uint32_t i = 0; i < 8 * N_BANKS; i++) {
      if(i < N_el) {
        pSrc[i] = (int16_t)((rand() % (upper - lower + 1)) + lower);
      } else {
        pSrc[i] = (int16_t) 0;
      }
      pDst[i] = (int16_t) 0;
    }
    #ifdef MEMSIZED
    for (uint32_t i = 0; i < 8 * N_BANKS; i++) {
      pCoef16_src[i] = (int16_t) 0;
      pCoef16_dst[i] = (int16_t) 0;
    }
    for (uint32_t ic = 0; ic < (N_CSAMPLES / 4); ic++) {
      *(v2s *)&pCoef16_src[2U * ic] = *(v2s *)&twiddleCoef_q16[2U * ic];
      *(v2s *)&pCoef16_src[2U * (ic + 1 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (ic * 2U)];
      *(v2s *)&pCoef16_src[2U * (ic + 2 * N_BANKS)] = *(v2s *)&twiddleCoef_q16[2U * (ic * 3U)];
    }
    #endif
}

int volatile error __attribute__((section(".l1")));
int main() {

    uint32_t core_id = mempool_get_core_id();
    mempool_barrier_init(core_id);

/* SINGLE-CORE */

#ifdef SINGLE

    if (core_id == 0)  {

      printf("On the run...\n");
      error = 0;
      initialize_vector(pSrc, pDst, N_RSAMPLES);

  #ifdef  TEST_16
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 16,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_16,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_16_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();

  #elif   defined(TEST_32)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 32,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_32,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_32_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_64)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 64,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_64,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_128)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 128,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_128,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_128_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_256)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 256,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_256,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_512)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 512,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_512,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_512_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_1024)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 1024,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_1024,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_2048)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 2048,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_2048,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_2048_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #elif   defined(TEST_4096)
      mempool_start_benchmark();
      mempool_cfft_q16s(  (uint16_t) 4096,
                          twiddleCoef_q16,
                          BitRevIndexTable_fixed_4096,
                          pSrc,
                          BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                          0, BIT_REV);
      mempool_stop_benchmark();
  #endif

      printf("Done SINGLE!\n");
  #ifdef PRINT_SINGLE
      for(uint32_t i=0; i<N_RSAMPLES; i+=2) {
        printf("{%6d;%6d } \n", pSrc[i], pSrc[i+1]);
      }
  #endif

    }
    mempool_barrier(NUM_CORES);

#endif


/* PARALLEL-CORE */

#ifdef PARALLEL

    if (core_id == 0)  {
      printf("On the run...\n");
      error = 0;
      initialize_vector(pSrc, pDst, N_RSAMPLES);
    }
    mempool_barrier(NUM_CORES);

  #ifdef  TEST_16

    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 16,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_16,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_16_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

  #elif   defined(TEST_32)

    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 32,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_32,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_32_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

  #elif   defined(TEST_64)

    #ifdef MEMSIZED

    #ifdef TWIDDLE_MODIFIER
    if(core_id < 4) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 64,
                                twiddleCoef_q16,
                                BitRevIndexTable_fixed_64,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                                0, BIT_REV, 4);
    mempool_stop_benchmark();
    }
    #else
    if(core_id < 4) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 64,
                                pCoef16_src,
                                pCoef16_dst,
                                BitRevIndexTable_fixed_64,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                                0, BIT_REV, 4);
    mempool_stop_benchmark();
    }
    #endif

    #else
    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 64,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_64,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_64_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #endif

  #elif   defined(TEST_128)

    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 128,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_128,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_128_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

  #elif   defined(TEST_256)

    #ifdef MEMSIZED


    #ifdef TWIDDLE_MODIFIER
    if(core_id < 16) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 256,
                                twiddleCoef_q16,
                                BitRevIndexTable_fixed_256,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                                0, BIT_REV, 16);
    mempool_stop_benchmark();
    }
    #else
    if(core_id < 16) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 256,
                                pCoef16_src,
                                pCoef16_dst,
                                BitRevIndexTable_fixed_256,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                                0, BIT_REV, 16);
    mempool_stop_benchmark();
    }
    #endif


    #else
    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 256,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_256,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_256_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #endif

  #elif   defined(TEST_512)

    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 512,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_512,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_512_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

  #elif   defined(TEST_1024)

    #ifdef MEMSIZED

    #ifdef TWIDDLE_MODIFIER
    if (core_id < 64) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 1024,
                                twiddleCoef_q16,
                                BitRevIndexTable_fixed_1024,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                                0, BIT_REV, 64);
    mempool_stop_benchmark();
    }
    #else
    if (core_id < 64) {
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 1024,
                                pCoef16_src,
                                pCoef16_dst,
                                BitRevIndexTable_fixed_1024,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                                0, BIT_REV, 64);
    mempool_stop_benchmark();
    }
    #endif

    #else
    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 1024,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_1024,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_1024_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #endif

  #elif   defined(TEST_2048)

    mempool_start_benchmark();
    mempool_cfft_q16p(  (uint16_t) 2048,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_2048,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_2048_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();

  #elif   defined(TEST_4096)

    #ifdef MEMSIZED

    #ifdef TWIDDLE_MODIFIER
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 4096,
                                twiddleCoef_q16,
                                BitRevIndexTable_fixed_4096,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                                0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #else
    mempool_start_benchmark();
    mempool_cfft_memsized_q16p( (uint16_t) 4096,
                                pCoef16_src,
                                pCoef16_dst,
                                BitRevIndexTable_fixed_4096,
                                pSrc,
                                pDst,
                                BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                                0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #endif

    #else
    mempool_start_benchmark();
    mempool_cfft_q16p( (uint16_t) 4096,
                        twiddleCoef_q16,
                        BitRevIndexTable_fixed_4096,
                        pSrc,
                        BITREVINDEXTABLE_FIXED_4096_TABLE_LENGTH,
                        0, BIT_REV, NUM_CORES);
    mempool_stop_benchmark();
    #endif

  #endif

    if(core_id == 0) {
      printf("Done PARALLEL!\n");
  #ifdef PRINT_PARALLEL
    for(uint32_t i = 0; i < N_RSAMPLES; i += 2) {
      printf("{%6d;%6d } \n", pSrc[i], pSrc[i + 1]);
    }
  #endif
    }
    mempool_barrier(NUM_CORES);

#endif


  return error;

}
