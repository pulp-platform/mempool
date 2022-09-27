// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define N 4
#define N_COL 1
#define N_ROW 1
//#define N_DEC 4096

//#define SINGLE
#define PARALLEL
#define N_BANKS (NUM_CORES * 4)

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
#if defined(PARALLEL)
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
#else
int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
#endif

#if defined(SINGLE)
#include "mempool_cholesky_q32s_schedule.h"
// Driver program
void single_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
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
#include "mempool_cholesky_q32p_schedule.h"
// Driver program
void parallel() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = (N / 4);
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

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

  /* Benchmark */
  if (core_id < N_COL * nPE) {
    mempool_start_benchmark();
    mempool_cholesky_q32p_fold(In_matrix, In_matrix, LL_matrix, LR_matrix, N,
                               N_ROW, N_COL, FIXED_POINT, nPE);
    // mempool_log_partial_barrier(2, core_id, nPE);
    // mempool_log_barrier(2, core_id);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}
#endif

int main() {

#if defined(SINGLE)
  single_core();
#endif

#if defined(PARALLEL)
  parallel();
#endif

  return 0;
}
