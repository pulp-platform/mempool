// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_cholesky_q16s.h"
#include "data_cholesky_q16.h"

#define SINGLE

int16_t l1_GIn[2 * dim_N * dim_N * N_SAMPLES]
    __attribute__((section(".l1_prio")));
int16_t l1_LOut[2 * dim_N * dim_N * N_SAMPLES]
    __attribute__((section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_GIn, l2_GIn,
                        dim_N * dim_N * N_SAMPLES * sizeof(int32_t));
    dma_memcpy_blocking(l1_LOut, l2_LOut,
                        dim_N * dim_N * N_SAMPLES * sizeof(int32_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#ifdef SINGLE
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_q16vecs(l1_GIn, l1_LOut, dim_N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  for (uint32_t i = core_id; i < N_SAMPLES; i += num_cores) {
    mempool_start_benchmark();
    __fp16 *ptr_in_matrix = l1_GIn + i * 2 * dim_N * dim_N;
    __fp16 *ptr_out_matrix = l1_LOut + i * 2 * dim_N * dim_N;
    mempool_cholesky_q16s(ptr_in_matrix, ptr_out_matrix, dim_N);
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  mempool_check_q16(l1_LOut, l2_LOut, 2 * dim_N * dim_N, 16, 0);
  mempool_barrier(num_cores);
  return 0;
}
