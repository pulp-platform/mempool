// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define HALF (1023)
#define FIX_DIV(a, b) ((int32_t)((a << FIXED_POINT) / b))
#define FIX_MUL(a, b) ((int32_t)((a * b + HALF) >> FIXED_POINT))
#define ABS(a) (a > 0 ? a : -a)
#define SINGLE
//#define PARALLEL
//#define SCHEDULING
//#define LINSOLVER

#include "data_cholesky_q32.h"

#include "baremetal/mempool_cholesky_q32p.h"
#include "baremetal/mempool_cholesky_q32s.h"
#include "baremetal/mempool_linearsolver_q32p.h"
#include "baremetal/mempool_linearsolver_q32s.h"

#ifndef SCHEDULING
#define N_COL 1
#define N_ROW 1
int32_t l1_A[matrix_N * matrix_N]
    __attribute__((aligned(NUM_BANKS), section(".l1")));
int32_t l1_L[matrix_N * matrix_N]
    __attribute__((aligned(NUM_BANKS), section(".l1")));
int32_t l1_y[matrix_N] __attribute__((aligned(NUM_BANKS), section(".l1")));
#else
int32_t l1_AA[matrix_N * NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
int32_t l1_LL[N_ROW * matrix_N * NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
int32_t l1_LR[N_ROW * matrix_N * NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
int32_t l1_yy[NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
#endif

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

// Initialize
#if defined(SCHEDULING)
  if (core_id == 0) {
    for (uint32_t i = 0; i < matrix_N; i++) {
      for (uint32_t idx_col = 0; idx_col < N_COL; idx_col++) {
        l1_yy[idx_col * matrix_N + i] = l2_y[i];
        for (uint32_t j = 0; j < matrix_N; j++) {
          l1_AA[idx_col * matrix_N + i * NUM_BANKS + j] =
              l2_A[i * matrix_N + j];
        }
      }
    }
    for (uint32_t i = 0; i < N_ROW * matrix_N * NUM_BANKS; i++) {
      l1_LL[i] = 0;
      l1_LR[i] = 0;
    }
  }
#else
  if (core_id == 0) {
    dma_memcpy_blocking(l1_A, l2_A, matrix_N * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(l1_L, l2_L, matrix_N * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(l1_y, l2_y, matrix_N * sizeof(int32_t));
  }
#endif
  mempool_barrier(num_cores);

  // Benchmark
#if defined(SINGLE)
  if (core_id == 0) {
    mempool_start_benchmark();
    // TEST #1 SINGLE-CORE CHOLESKY DECOMPOSITION
    mempool_cholesky_crout_q32s(l1_A, l1_L, matrix_N);
    // // TEST #2 SINGLE-CORE LINEAR-SYSTEM SOLUTION
    // mempool_linearsolver_q32s(l1_A, l1_L, l1_y, matrix_N);
    // mempool_uprtrisolver_q32s(l1_L, l1_y, matrix_N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL)
  // TEST #3 PARALLEL CHOLESKY DECOMPOSITION
  // No trivial parallelization of linearsolver kernels
  mempool_start_benchmark();
  mempool_cholesky_q32p(l1_A, l1_L, matrix_N);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);
#endif

#if defined(SCHEDULING)
  /* Each decomposition is finely-grained parallelized over multiple cores */
  uint32_t nPE = (matrix_N / 4);
  if ((nPE > 1) && (core_id < N_COL * nPE)) {
    mempool_start_benchmark();
    // TEST #4 FINE-GRAINED PARALLEL CHOLESKY DECOMPOSITION x N_ROW x N_COL
    mempool_cholesky_fold_schedule_q32p(l1_AA, l1_AA, l1_LL, l1_LR, matrix_N,
                                        N_ROW, N_COL);
    // // TEST #5 FINE-GRAINED PARALLEL LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
    // mempool_linearsolver_fold_q32p(l1_AA, l1_AA, l1_LL, l1_LR, l1_yy,
    // matrix_N, N_ROW, N_COL);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  /* The decomposition is executed with a single-core. Each core gets a
   * different input problem. This is the specific case of the 4x4 matrix. */
  if ((nPE == 1) && (core_id < N_COL * nPE)) {
    mempool_start_benchmark();
    // TEST #6 SINGLE-CORE CHOLESKY DECOMPOSITION x N_ROW x N_COL
    mempool_cholesky_schedule_q32s(l1_AA, l1_LL, matrix_N, N_ROW, N_COL);
    // // TEST #7 SINGLE-CORE LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
    // mempool_linearsolver_q32s(l1_AA, l1_LL, l1_yy, matrix_N, N_ROW, N_COL);
    mempool_stop_benchmark();
  }
#endif

  return 0;
}
