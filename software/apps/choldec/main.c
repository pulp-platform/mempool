// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define N 4
#define N_BANKS (NUM_CORES * 4)

//#define SINGLE
//#define PARALLEL
//#define FOLDED

//#define BANACHIEWICZ
#define CROUT
#define VERBOSE

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_sqrt_q32s.h"

#include "mempool_cholesky_q32p.h"
#include "mempool_cholesky_q32s.h"

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));

int32_t LL_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));

int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));

void initialize() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix(In, 1, N, -15, 557, -300, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
#if defined(FOLDED)
  init_matrix_zeros(LL_matrix, N, N_BANKS, core_id);
  init_matrix_zeros(LR_matrix, N, N_BANKS, core_id);
#else
  init_matrix_zeros(L_matrix, N, N, core_id);
#endif
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
  }
  mempool_barrier(num_cores);
}

#if defined(SINGLE)
// Driver program
void single_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_q32s(M_matrix, L_matrix, N);
    // mempool_linearsolver_q32s(M_matrix, L_matrix, In, N);
    // mempool_uprtrisolver_q32s(L_matrix, In, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#ifdef VERBOSE
  if (core_id == 0) {
    display(L_matrix, N, N);
    display(In, 1, N);
  }
  mempool_barrier(num_cores);
#endif
}
#endif

#if defined(PARALLEL)
// Driver program
void parallel() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  mempool_start_benchmark();
  mempool_cholesky_q32p(M_matrix, L_matrix, N);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
#ifdef VERBOSE
  if (core_id == 0) {
    display(L_matrix, N, N);
  }
  mempool_barrier(num_cores);
#endif
}
#endif

#if defined(FOLDED)
// Driver program
void parallel_folded() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  if (core_id < nPE) {
    mempool_start_benchmark();
    mempool_cholesky_q32p_fold(M_matrix, M_matrix, LL_matrix, LR_matrix, N,
                               nPE);
    // mempool_linearsolver_q32p_fold(M_matrix, M_matrix, LL_matrix, LR_matrix,
    // In, N, nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#ifdef VERBOSE
  if (core_id == 0) {
    display(LL_matrix, N, N);
    display(LR_matrix, N, N);
    display(In, 1, N);
  }
  mempool_barrier(num_cores);
#endif
}
#endif

int main() {

#if defined(SINGLE)
  single_core();
#endif

#if defined(PARALLEL)
  parallel();
#endif

#if defined(FOLDED)
  parallel_folded();
#endif

  return 0;
}
