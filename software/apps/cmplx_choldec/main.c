// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define N 8
#define N_BANKS (NUM_CORES * 4)

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_cmplx_cholesky_q16s.h"

int32_t M[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t L[N * N] __attribute__((aligned(N_BANKS), section(".l1")));

// Driver program
void single_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  /* Initialize matrices */
  init_matrix(M, N, N, core_id);
  init_matrix_zeros(L, N, N, core_id);
  mempool_barrier(num_cores);

  /* Benchmark */
  if (core_id == 0) {
    mempool_cholesky_q32s(M, L, N, FIXED_POINT);
    mempool_start_benchmark();
    mempool_cholesky_q32s(M, L, N, FIXED_POINT);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}

int main() {
  single_core();
  return 0;
}
