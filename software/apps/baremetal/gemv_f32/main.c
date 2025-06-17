// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_gemv_f32.h"
uint32_t red_barrier[NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float sum[NUM_BANKS] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_gemv_f32.h"

float l1_A[matrix_N * matrix_P] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float l1_X[matrix_N] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
float l1_Y[matrix_P] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));


int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1_A, l2_A, matrix_N * matrix_P * sizeof(int32_t));
    dma_memcpy_blocking(l1_X, l2_X, matrix_N * sizeof(int32_t));
  }
  for (uint32_t k = core_id; k < NUM_BANKS; k += num_cores) {
    sum[k] = 0;
    red_barrier[k] = 0;
  }
  mempool_barrier(num_cores);

  mempool_start_benchmark();
  gemv_f32p_local_unrolled4(l1_A, l1_X, l1_Y, matrix_N, matrix_P);
  mempool_stop_benchmark();

  // Check results
  mempool_check_f32(l1_Y, l2_Y, matrix_P, 0.01f, 0);
  mempool_barrier(num_cores);

  return 0;
}
