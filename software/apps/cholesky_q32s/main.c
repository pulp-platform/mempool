// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N_BANKS (NUM_CORES * 4)
/* Dimension of the input matrix */
#define N 4

/* TEST1 Single-Core Colesky decomposition --> #define SINGLE
   TEST2 Single-Core system inversion --> #define SINGLE #define LINSOLVER
   TEST3 Parallel Cholesky decomposition --> #define PARALLEL
   TEST4 Parallel folded Cholesky decomposition --> #define FOLDED
   TEST5 Parallel folded system inversion --> #define FOLDED LINSOLVER */
//#define SINGLE
//#define PARALLEL
//#define FOLDED
//#define LINSOLVER
/* Define VERBOSE to see the matrix printed. */
#define VERBOSE

/* DATA */
int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LL_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));

#include "initialization.h"
#include "kernel/mempool_cholesky_q32s.h"
#include "kernel/mempool_linearsolver_q32s.h"

#include "kernel/mempool_cholesky_q32p.h"
#include "kernel/mempool_linearsolver_q32p.h"

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

// Driver program
void single_core_cholesky() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_crout_q32s(M_matrix, L_matrix, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}

// Driver program
void single_core_linearsolver() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_linearsolver_q32s(M_matrix, L_matrix, In, N);
    mempool_uprtrisolver_q32s(L_matrix, In, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}

// Driver program
void parallel_cholesky() {
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
}

// Driver program
void parallel_cholesky_folded() {
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

// Driver program
void parallel_linearsolver_folded() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize();
  /* Benchmark */
  uint32_t nPE = N / 4;
  if (core_id < nPE) {
    mempool_start_benchmark();
    mempool_linearsolver_q32p_fold(M_matrix, M_matrix, LL_matrix, LR_matrix, In,
                                   In, N, nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

#ifdef SINGLE
  single_core_cholesky();
#endif
#if defined(SINGLE) && defined(LINEARSOLVER)
  single_core_linearsolver();
#endif
#ifdef PARALLEL
  parallel_cholesky();
#endif
#if defined(PARALLEL) && defined(FOLDED)
  parallel_cholesky_folded();
#endif
#if defined(PARALLEL) && defined(FOLDED) && defined(LINEARSOLVER)
  parallel_linearsolver_folded();
#endif

#if defined(VERBOSE) && defined(FOLDED)
  if (core_id == 0) {
    display(LL_matrix, N, N);
    display(LR_matrix, N, N);
    display(In, 1, N);
  }
  mempool_barrier(num_cores);
#elif defined(VERBOSE)
  if (core_id == 0) {
    display(L_matrix, N, N);
    display(In, 1, N);
  }
  mempool_barrier(num_cores);
#endif
  return 0;
}
