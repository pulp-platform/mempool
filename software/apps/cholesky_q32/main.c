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
//#define SCHEDULING
//#define LINSOLVE4

#define N_COL 1
#define N_ROW 1
#define N_ITR 1

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
#ifndef SCHEDULING
int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));
#else
// Matrices to generate the hermitian
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
// Outputs and input vector for linear system solution
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N_BANKS] __attribute__((aligned(N_BANKS), section(".l1")));
#endif

#include "initialization.h"
#include "mempool_cholesky_q32s.h"
#include "mempool_linearsolver_q32s.h"

#include "mempool_cholesky_q32p.h"
#include "mempool_linearsolver_q32p.h"

void initialize() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  /* Initialize input matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);

#ifndef SCHEDULING

  init_matrix_zeros(L_matrix, N, N, core_id);
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
    printf("Done initialization.\n");
  }
  mempool_barrier(num_cores);
#ifdef LINEARSOLVER
  init_matrix(In, 1, N, -156, 427, -219, core_id);
  mempool_barrier(num_cores);
#endif

#else

  init_matrix_zeros(In_matrix, N, N_BANKS, core_id);
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
#ifdef LINEARSOLVER
  init_matrix(In, 1, N_BANKS, -156, 427, -219, core_id);
  mempool_barrier(num_cores);
#endif

#endif
  return;
}

/* BENCHMARK */

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize();

#if defined(SINGLE)
  if (core_id == 0) {
    mempool_start_benchmark();
    for (uint32_t i = 0; i < N_ITR; i++) {
#ifndef LINEARSOLVER
      // TEST #1 SINGLE-CORE CHOLESKY DECOMPOSITION
      mempool_cholesky_crout_q32s(M_matrix, L_matrix, N);
#else
      // TEST #2 SINGLE-CORE LINEAR-SYSTEM SOLUTION
      mempool_linearsolver_q32s(M_matrix, L_matrix, In, N);
      mempool_uprtrisolver_q32s(L_matrix, In, N);
#endif
    }
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL) && !defined(SCHEDULING)
#ifndef LINEARSOLVER
  // TEST #3 PARALLEL CHOLESKY DECOMPOSITION
  mempool_start_benchmark();
  mempool_cholesky_q32p(M_matrix, L_matrix, N);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
#else
// No trivial parallelization of linearsolver kernels
#endif
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL) && defined(SCHEDULING)
  uint32_t nPE = (N / 4);
  if (nPE > 1) {
    /* Each decomposition is finely-grained parallelized over multiple cores */
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
#ifndef LINEARSOLVER
      // TEST #4 FINE-GRAINED PARALLEL CHOLESKY DECOMPOSITION x N_ROW x N_COL
      mempool_cholesky_fold_schedule_q32p(In_matrix, In_matrix, LL_matrix,
                                          LR_matrix, N, N_ROW, N_COL);
#else
      // TEST #5 FINE-GRAINED PARALLEL LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
      mempool_linearsolver_fold_q32p(In_matrix, In_matrix, LL_matrix, LR_matrix,
                                     In, N, N_ROW, N_COL);
#endif
      mempool_stop_benchmark();
    }
  }
  if (nPE == 1) {
    /* The decomposition is executed with a single-core. Each core gets a
     * different input problem. This is the specific case of the 4x4 matrix. */
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
#ifndef LINEARSOLVER
      // TEST #6 SINGLE-CORE CHOLESKY DECOMPOSITION x N_ROW x N_COL
      mempool_cholesky_schedule_q32s(In_matrix, LL_matrix, N, N_ROW, N_COL);
#else
      // TEST #7 SINGLE-CORE LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
      mempool_linearsolver_q32s(In_matrix, LL_matrix, In, N, N_ROW, N_COL);
#endif
      mempool_stop_benchmark();
    }
  }
  mempool_barrier(num_cores);
#endif

  return 0;
}
