// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <limits.h>
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

/* CFFT mempool libraries */
#include "data/data_cfft_radix2_q16.h"
#include "kernel/mempool_radix2_cfft_q16p.h"
#include "kernel/mempool_radix2_cfft_q16s.h"

#define PARALLEL
#define SINGLE

/* CFFT mempool data */
int16_t l1_pSrc[N_RSAMPLES]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
int16_t l1_twiddleCoef_q16[6 * N_CSAMPLES / 4]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(4 * N_BANKS), section(".l1_prio")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1_pSrc, l2_pSrc, N_CSAMPLES * sizeof(int32_t));
    dma_memcpy_blocking(l1_twiddleCoef_q16, l2_twiddleCoef_q16,
                        (3 * N_CSAMPLES / 4) * sizeof(int32_t));
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  /* SINGLE-CORE */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_radix2_cfft_q16s((uint16_t)16, l1_twiddleCoef_q16,
                             l1_BitRevIndexTable, l1_pSrc,
                             BITREVINDEXTABLE_LENGTH, 0, 0);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

  /* PARALLEL-CORE */
#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix2_cfft_q16p((uint16_t)16, l1_twiddleCoef_q16,
                           l1_BitRevIndexTable, l1_pSrc,
                           BITREVINDEXTABLE_LENGTH, 0, 0, num_cores);
  mempool_stop_benchmark();
#endif

  if (core_id == 0) {
    for (uint32_t i = 0; i < N_RSAMPLES; i += 2) {
      printf("{%6d;%6d } \n", l1_pSrc[i], l1_pSrc[i + 1]);
    }
    printf("Done!\n");
  }
  mempool_barrier(num_cores);
  return 0;
}
