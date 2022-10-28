// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "define.h"

#include "initialization.h"
#include "mempool_sqrt_q32s.h"

#include "mempool_cholesky_q32p_schedule.h"
#include "mempool_cholesky_q32s_schedule.h"
#include "mempool_linsolver_q32p_schedule.h"
#include "mempool_linsolver_q32s_schedule.h"

void initialize() {

#if defined(SINGLE)
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  /* Initialize matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
  init_matrix_zeros(L_matrix, N, N, core_id);
#if defined(LINSOLVER)
  init_matrix(In, 1, N, -156, 427, -219, core_id);
#endif
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
    printf("Done initialization.\n");
  }
  mempool_barrier(num_cores);

#elif defined(PARALLEL)
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  /* Initialize input matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
  init_matrix_zeros(In_matrix, N, N_BANKS, core_id);
#if defined(LINSOLVER)
  init_matrix(In, 1, N_BANKS, -156, 427, -219, core_id);
#endif
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
}

#if defined(SINGLE)
// Driver program
void single_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  initialize();
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    for (uint32_t i = 0; i < N_DEC; i++) {
#if defined(LINSOLVER)
      mempool_linearsolver_q32s(M_matrix, L_matrix, In, N);
#else
      mempool_cholesky_q32s(M_matrix, L_matrix, N);
#endif
    }
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}
#endif

#if defined(PARALLEL)
// Driver program
void parallel() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = (N / 4);
  mempool_barrier_init(core_id);
  initialize();

  /* Benchmark */
  /* The decomposition is finely-grained parallelized over multiple cores */
  if (nPE > 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
#if defined(LINSOLVER)
      mempool_linsolver_q32p_fold(In_matrix, In_matrix, LL_matrix, LR_matrix,
                                  In, N, N_ROW, N_COL);
#else
      mempool_cholesky_q32p_fold(In_matrix, In_matrix, LL_matrix, LR_matrix, N,
                                 N_ROW, N_COL);
#endif
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
  /* The decomposition is executed with a single-core. This is the specific
     case of the 4x4 matrix */
  if (nPE == 1) {
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
#if defined(LINSOLVER)
      mempool_linearsolver_q32s_schedule(In_matrix, LL_matrix, In, N, N_ROW,
                                         N_COL);
#else
      mempool_cholesky_q32s_schedule(In_matrix, LL_matrix, N, N_ROW, N_COL);
#endif
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
  }
}
#endif

int main() {

#if defined(SINGLE)
  single_core();
#elif defined(PARALLEL)
  parallel();
#endif

  return 0;
}
