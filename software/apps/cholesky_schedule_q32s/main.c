// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N_BANKS (NUM_CORES * 4)

/* Matrix dimension */
#define N 4

#define SINGLE
//#define PARALLEL
//#define LINSOLVER

#define N_COL 256
#define N_ROW 1
#define N_DEC 2

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));

#if defined(SINGLE)
int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));
#endif

#if defined(PARALLEL)
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N_BANKS] __attribute__((aligned(N_BANKS), section(".l1")));
#endif

#include "initialization.h"
#include "kernel/mempool_cholesky_q32s.h"
#include "kernel/mempool_linearsolver_q32s.h"

#include "kernel/mempool_cholesky_q32p.h"
#include "kernel/mempool_linearsolver_q32p.h"

void initialize() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  /* Initialization input vector */
#if defined(LINSOLVER) && defined(SINGLE)
  init_matrix(In, 1, N, -156, 427, -219, core_id);
#elif defined(LINSOLVER) && defined(PARALLEL)
  init_matrix(In, 1, N_BANKS, -156, 427, -219, core_id);
#endif
  mempool_barrier(num_cores);

  /* Initialize input matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
#if defined(SINGLE)
  init_matrix_zeros(L_matrix, N, N, core_id);
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
    printf("Done initialization.\n");
  }
  mempool_barrier(num_cores);

#elif defined(PARALLEL)
  init_matrix_zeros(In_matrix, N, N_BANKS, core_id);
  /* Initialize output matrices */
  init_matrix_zeros(LL_matrix, N_ROW * N, N_BANKS, core_id);
  init_matrix_zeros(LR_matrix, N_ROW * N, N_BANKS, core_id);
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
    for (uint32_t idx_col = 0; idx_col < N_COL; idx_col++) {
      for (uint32_t i = 0; i < N; i++) {
        for (uint32_t j = 0; j < N; j++) {
          In_matrix[idx_col * N + i * N_BANKS + j] = M_matrix[i * N + j];
        }
      }
    }
    printf("Done initialization.\n");
  }
  mempool_barrier(num_cores);

#endif

  return;
}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize();

#if defined(SINGLE)
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    for (uint32_t i = 0; i < N_DEC; i++) {
      mempool_cholesky_crout_q32s(M_matrix, L_matrix, N);
    }
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(SINGLE) && defined(LINEARSOLVER)
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    for (uint32_t i = 0; i < N_DEC; i++) {
      mempool_linearsolver_q32s(M_matrix, L_matrix, In, N);
      mempool_uprtrisolver_q32s(L_matrix, In, N);
    }
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  /* Benchmark */
  uint32_t nPE = (N / 4);
  /* The decomposition is finely-grained parallelized over multiple cores */
  if (nPE > 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_fold_schedule_q32p(In_matrix, In_matrix, LL_matrix,
                                          LR_matrix, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
  /* The decomposition is executed with a single-core. Each core gets a
   * different input problem. This is the specific case of the 4x4 matrix. */
  if (nPE == 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_schedule_q32s(In_matrix, LL_matrix, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
#endif

#if defined(PARALLEL) && defined(LINEARSOLVER)
  /* Benchmark */
  uint32_t nPE = (N / 4);
  /* The decomposition is finely-grained parallelized over multiple cores */
  if (nPE > 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_linearsolver_fold_schedule_q32p(In_matrix, In_matrix, LL_matrix,
                                              LR_matrix, In, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
  /* The decomposition is executed with a single-core. Each core gets a
   * different input problem. This is the specific case of the 4x4 matrix. */
  if (nPE == 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_linearsolver_schedule_q32s(In_matrix, LL_matrix, In, N, N_ROW,
                                         N_COL);
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
#endif

  return 0;
}
