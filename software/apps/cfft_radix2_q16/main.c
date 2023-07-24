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
int16_t pSrc[N_RSAMPLES] __attribute__((aligned(N_CSAMPLES), section(".l1")));

void initialize_l1(int16_t *pSrc, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for (uint32_t i = core_id; i < N_el; i += num_cores) {
    pSrc[i] = vector_inp[i];
  }
}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  initialize_l1(pSrc, N_RSAMPLES);
  mempool_barrier(num_cores);

  /* SINGLE-CORE */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_radix2_cfft_q16s((uint16_t)16, twiddleCoef_q16, BitRevIndexTable,
                             pSrc, BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, 0);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

  /* PARALLEL-CORE */
#ifdef PARALLEL
  mempool_start_benchmark();
  mempool_radix2_cfft_q16p((uint16_t)16, twiddleCoef_q16, BitRevIndexTable,
                           pSrc, BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 0, 0,
                           num_cores);
  mempool_stop_benchmark();
#endif

  if (core_id == 0) {
    for (uint32_t i = 0; i < N_RSAMPLES; i += 2) {
      printf("{%6d;%6d } \n", pSrc[i], pSrc[i + 1]);
    }
    printf("Done!\n");
  }
  mempool_barrier(num_cores);
  return 0;
}
