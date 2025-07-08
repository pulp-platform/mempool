// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <math.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_cholesky_f16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_cholesky_f16s.h"

/*
======================
Parameters and defines

SINGLE: When defined runs single-core Cholesky Decomposition.
PARALLEL: When defined runs parallel Cholesky Decomposition.
FOLDED: When defined 1 intermediate results are folded in memory.
*/

#define SINGLE
#define FOLDED (0)

__fp16 l1_GIn[2 * matrix_N * matrix_N * N_SAMPLES]
    __attribute__((section(".l1_prio")));
__fp16 l1_LOut[2 * matrix_N * matrix_N * N_SAMPLES]
    __attribute__((section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_GIn, l2_GIn,
                        matrix_N * matrix_N * N_SAMPLES * sizeof(int32_t));
    dma_memcpy_blocking(l1_LOut, l2_LOut,
                        matrix_N * matrix_N * N_SAMPLES * sizeof(int32_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#ifdef SINGLE
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_f16vecs(l1_GIn, l1_LOut, matrix_N, FOLDED);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  for (uint32_t i = core_id; i < N_SAMPLES; i += num_cores) {
    mempool_start_benchmark();
    __fp16 *ptr_in_matrix = l1_GIn + i * 2 * matrix_N * matrix_N;
    __fp16 *ptr_out_matrix = l1_LOut + i * 2 * matrix_N * matrix_N;
    mempool_cholesky_f16vecs(ptr_in_matrix, ptr_out_matrix, matrix_N, FOLDED);
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  mempool_check_f16(l1_LOut, l2_LOut, 2 * matrix_N * matrix_N, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
