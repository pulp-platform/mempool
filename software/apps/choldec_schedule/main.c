// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define N 4
#define N_COL 1024
#define N_ROW 3
//#define N_DEC 4096

//#define SINGLE
//#define PARALLEL
#define LINSOLVER
#define N_BANKS (NUM_CORES * 4)

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_sqrt_q32s.h"

#include "mempool_cholesky_q32p_schedule.h"
#include "mempool_cholesky_q32s_schedule.h"
#include "mempool_linsolver_q32p_schedule.h"

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));

#if defined(SINGLE)
int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
#elif defined(PARALLEL)
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
#elif defined(LINSOLVER)
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N_BANKS] __attribute__((aligned(N_BANKS), section(".l1")));
#endif

void initialize() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
#if defined(SINGLE)
  /* Initialize matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
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
  /* Initialize matrices */
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
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
#elif defined(LINSOLVER)
  /* Initialize matrices */
  init_matrix(In_matrix, N, N_BANKS, -156, 427, -219, core_id);
  init_matrix(In, 1, N_BANKS, -156, 427, -219, core_id);
  init_matrix_zeros(LL_matrix, N_ROW * N, N_BANKS, core_id);
  init_matrix_zeros(LR_matrix, N_ROW * N, N_BANKS, core_id);
  mempool_barrier(num_cores);
  /* Create positive definite matrix */
  //  if (core_id == 0) {
  //    transpose(A_matrix, AT_matrix, N);
  //    matrixmult(AT_matrix, A_matrix, M_matrix, N);
  //    for (uint32_t idx_col = 0; idx_col < N_COL; idx_col++) {
  //      for (uint32_t i = 0; i < N; i++) {
  //          In[idx_col * N + i] = 100;
  //        for (uint32_t j = 0; j < N; j++) {
  //          In_matrix[idx_col * N + i * N_BANKS + j] = M_matrix[i * N + j];
  //        }
  //      }
  //    }
  //    printf("Done initialization.\n");
  //  }
  mempool_barrier(num_cores);
#endif
}

#if defined(SINGLE)
// Driver program
void single_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  initialize();

  /* Benchmark */
  if (core_id == 0) {
    mempool_cholesky_q32s(M_matrix, L_matrix, N, FIXED_POINT);
    mempool_start_benchmark();
    for (uint32_t i = 0; i < N_DEC; i++) {
      mempool_cholesky_q32s(M_matrix, L_matrix, N, FIXED_POINT);
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
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  initialize();

  /* Benchmark */
  if (core_id < N_COL * nPE) {
    mempool_start_benchmark();
    mempool_cholesky_q32p_fold(In_matrix, In_matrix, LL_matrix, LR_matrix, N,
                               N_ROW, N_COL);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}
#endif

#if defined(LINSOLVER)
// Driver program
void linsolver() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = (N / 4);
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  initialize();

  //  /* Benchmark */
  //  if (core_id < N_COL * nPE) {
  //    mempool_start_benchmark();
  //    mempool_linsolver_q32p_fold(In_matrix, In_matrix, LL_matrix,
  //    LR_matrix, In, N, N_ROW, N_COL);
  //    mempool_stop_benchmark();
  //  }
  //  mempool_barrier(num_cores);

  if (core_id < N_COL * nPE) {
    mempool_start_benchmark();
    mempool_linearsolver_q32s_schedule(In_matrix, LL_matrix, In, N, N_ROW,
                                       N_COL);
    mempool_barrier(NUM_CORES);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}
#endif

int main() {
#if defined(SINGLE)
  single_core();
#elif defined(PARALLEL)
  parallel();
#elif defined(LINSOLVER)
  linsolver();
#endif

  return 0;
}
