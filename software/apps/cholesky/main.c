// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#define N 8
#define N_ROW 1
#define N_COL 2
#define N_ITR 1
#define N_BANKS (NUM_CORES * 4)

//#define FOLDED

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_sqrt_q32s.h"

#include "mempool_cholesky_q32p.h"
#include "mempool_cholesky_q32s.h"
#include "mempool_linearsolver_q32p.h"
#include "mempool_linearsolver_q32s.h"

#include "mempool_choleskywrappers.h"

/* DATA INITALIZATIONS */

#if defined(FOLDED)

int32_t LL_matrix[N_ROW * N_BANKS * N]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N_BANKS * N]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N_BANKS] __attribute__((aligned(N_BANKS), section(".l1")));
void initialize() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  /* Create positive definite matrix */
  int32_t A_matrix[N * N];
  int32_t AT_matrix[N * N];
  int32_t M_matrix[N * N];
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
  }
  mempool_barrier(num_cores);
  /* Initialize matrices */
  init_matrix_zeros(LL_matrix, N_ROW * N, N_BANKS, core_id);
  init_matrix_zeros(LR_matrix, N_ROW * N, N_BANKS, core_id);
  init_matrix(In, 1, N_BANKS, -156, 427, -219, core_id);
  if (core_id == 0) {
    for (uint32_t idx_col = 0; idx_col < N_COL; idx_col++) {
      for (uint32_t i = 0; i < N; i++) {
        for (uint32_t j = 0; j < N; j++) {
          In_matrix[i * N_BANKS + j + idx_col * N] = M_matrix[i * N + j];
        }
      }
    }
  }
  mempool_barrier(num_cores);
  return;
}

#else

int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));
void initialize() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  /* Create positive definite matrix */
  int32_t A_matrix[N * N];
  int32_t AT_matrix[N * N];
  int32_t M_matrix[N * N];
  init_matrix(A_matrix, N, N, -156, 427, -219, core_id);
  init_matrix_zeros(AT_matrix, N, N, core_id);
  init_matrix_zeros(M_matrix, N, N, core_id);
  if (core_id == 0) {
    transpose(A_matrix, AT_matrix, N);
    matrixmult(AT_matrix, A_matrix, M_matrix, N);
  }
  mempool_barrier(num_cores);
  /* Initialize matrices */
  init_matrix_zeros(L_matrix, N, N, core_id);
  init_matrix(In, 1, N, -156, 427, -219, core_id);
  if (core_id == 0) {
    for (uint32_t i = 0; i < N; i++) {
      for (uint32_t j = 0; j < N; j++) {
        In_matrix[i * N + j] = M_matrix[i * N + j];
      }
    }
  }
  mempool_barrier(num_cores);
  return;
}

#endif

/* BENCHMARKS */

#if defined(FOLDED)

/* Benchmark of a Fine-Grained parallelized Cholesky decomposition */
void benchmark_cholesky_q32p() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  if (core_id < nPE) {
    mempool_start_benchmark();
    mempool_cholesky_q32p_fld(In_matrix, In_matrix, LL_matrix, LR_matrix, N,
                              nPE);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

/* Benchmark of NCOL*NROW Fine-Grained parallelized Cholesky decompositions */
void benchmark_cholesky_q32p_schedule() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  if (core_id < nPE * N_COL) {
    mempool_start_benchmark();
    mempool_cholesky_q32p_fld_scheduler(In_matrix, In_matrix, LL_matrix,
                                        LR_matrix, N, N_ROW, N_COL);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

/* Benchmark of NCOL*NROW folded, Fine-Grained parallelized linear-system
 * solutions */
void benchmark_linearsolver_q32p_schedule() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  if (core_id < nPE * N_COL) {
    mempool_start_benchmark();
    mempool_linearsolver_q32p_fld_scheduler(In_matrix, In_matrix, LL_matrix,
                                            LR_matrix, In, N, N_ROW, N_COL);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

/* Benchmark of NCOL*NROW folded single-core 4x4 linear-system solutions */
void benchmark_linearsolver_q32s_schedule() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  if (core_id < nPE * N_COL) {
    mempool_start_benchmark();
    mempool_linearsolver_q32s_fld_scheduler(In_matrix, LL_matrix, In, N, N_ROW,
                                            N_COL);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

#else

/* Benchmark of a single-core Cholesky decomposition */
void benchmark_cholesky_q32s() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  mempool_cholesky_q32s(In_matrix, L_matrix, N);
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_q32s(In_matrix, L_matrix, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

/* Benchmark of Fine-Grained parallelized Cholesky decomposition */
void benchmark_cholesky_q32p() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  mempool_start_benchmark();
  mempool_cholesky_q32p(In_matrix, L_matrix, N);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
  return;
}

/* Benchmark of a single-core linear-system solution */
void benchmark_linearsolver_q32s() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t nPE = N / 4;
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  initialize();
  /* Benchmark */
  if (core_id < nPE * N_COL) {
    mempool_start_benchmark();
    mempool_linearsolver_q32s(In_matrix, L_matrix, In, N);
    // mempool_linearsolver_q32s_scheduler(In_matrix, In_matrix, LL_matrix,
    // LR_matrix, pIn, N, N_ITR);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  return;
}

#endif

int main() {

  /*CHOOSE ONE */

  // DEFINE "FOLDED" FOR THESE
  // Benchmark of a Fine-Grained parallelized Cholesky decomposition
  //    benchmark_cholesky_q32p();
  // Benchmark of NCOL*NROW folded Fine-Grained parallelized Cholesky
  // decompositions
  //    benchmark_cholesky_q32p_schedule();
  // Benchmark of NCOL*NROW folded, Fine-Grained parallelized linear-system
  // solutions */
  //    benchmark_linearsolver_q32p_schedule();
  // Benchmark of NCOL*NROW folded single-core 4x4 linear-system solutions
  //    benchmark_linearsolver_q32s_schedule();

  // Benchmark of a single-core Cholesky decomposition
  //   benchmark_cholesky_q32s();
  // Benchmark of Fine-Grained parallelized Cholesky decomposition
  //   benchmark_cholesky_q32p();
  // Benchmark of a single-core linear-system solution
  //   benchmark_linearsolver_q32s();

  return 0;
}
