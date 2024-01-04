// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

/* Constants */
#define N_BANKS (NUM_CORES * 4)
#define FIXED_POINT 10
#define HALF 1023
#define FIX_DIV(a, b) ((int32_t)((a << FIXED_POINT) / b))
#define FIX_MUL(a, b) ((int32_t)((a * b + HALF) >> FIXED_POINT))
#define ABS(a) (a > 0 ? a : -a)

#define SINGLE
//#define PARALLEL
//#define SCHEDULING
//#define LINEARSOLVER
#define N_COL 1
#define N_ROW 1

#include "data/data_cholesky_q32.h"
#include "kernel/mempool_cholesky_q32p.h"
#include "kernel/mempool_cholesky_q32s.h"
#include "kernel/mempool_linearsolver_q32p.h"
#include "kernel/mempool_linearsolver_q32s.h"

int32_t l1_GIn[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t l1_LOut[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t l1_y[N] __attribute__((aligned(N_BANKS), section(".l1")));

// Inputs and Outputs for folded execution
int32_t In_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LL_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N_ROW * N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N_BANKS] __attribute__((aligned(N_BANKS), section(".l1")));

/* BENCHMARK */

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1_GIn, l2_GIn, N * N * sizeof(int32_t));
    dma_memcpy_blocking(l1_LOut, l2_LOut, N * N * sizeof(int32_t));
  }
  // Copy matrix l1_GIn for folded execution
  for (uint32_t idx_col = core_id; idx_col < N_COL; idx_col += num_cores) {
    for (uint32_t i = 0; i < N; i++) {
      for (uint32_t j = 0; j < N; j++) {
        In_matrix[idx_col * N + i * N_BANKS + j] = l1_GIn[i * N + j];
      }
      In[idx_col * N + i] = l1_y[i];
    }
  }
  mempool_barrier(num_cores);

#if defined(SINGLE)
#ifndef LINEARSOLVER
  // TEST #1 SINGLE-CORE LINEAR-SYSTEM SOLUTION
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_crout_q32s(l1_GIn, l1_LOut, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

#else
  // TEST #2 SINGLE-CORE LINEAR-SYSTEM SOLUTION
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_crout_q32s(l1_GIn, l1_LOut, N);
    mempool_linearsolver_q32s(l1_GIn, l1_LOut, In, N);
    mempool_uprtrisolver_q32s(l1_LOut, In, N);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

#endif
#endif

#if defined(PARALLEL) && !defined(SCHEDULING)
#ifndef LINEARSOLVER
  // TEST #3 PARALLEL CHOLESKY DECOMPOSITION
  mempool_start_benchmark();
  mempool_cholesky_q32p(l1_GIn, l1_LOut, N);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

#else
// No trivial parallelization of linearsolver kernels
#endif
#endif

#if defined(PARALLEL) && defined(SCHEDULING)
#ifndef LINEARSOLVER
  // TEST #4 FINE-GRAINED PARALLEL CHOLESKY DECOMPOSITION x N_ROW x N_COL
  uint32_t nPE = (N / 4);
  if (nPE > 1) {
    /* Each decomposition is finely-grained parallelized over multiple cores */
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_fold_schedule_q32p(In_matrix, In_matrix, LL_matrix,
                                          LR_matrix, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
  }
  if (nPE == 1) {
    /* The decomposition is executed with a single-core. Each core gets a
     * different input problem. This is the specific case of the 4x4 matrix. */
    // TEST #5 SINGLE-CORE CHOLESKY DECOMPOSITION x N_ROW x N_COL
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_schedule_q32s(In_matrix, LL_matrix, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
  }
  mempool_barrier(num_cores);

#else
  // TEST #6 FINE-GRAINED PARALLEL LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
  uint32_t nPE = (N / 4);
  if (nPE > 1) {
    /* Each decomposition is finely-grained parallelized over multiple cores */
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_fold_schedule_q32p(In_matrix, In_matrix, LL_matrix,
                                          LR_matrix, N, N_ROW, N_COL);
      mempool_linearsolver_fold_q32p(In_matrix, In_matrix, LL_matrix, LR_matrix,
                                     In, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
  }
  if (nPE == 1) {
    /* The decomposition is executed with a single-core. Each core gets a
     * different input problem. This is the specific case of the 4x4 matrix. */
    // TEST #7 SINGLE-CORE LINEAR-SYSTEM SOLUTION x N_ROW x N_COL
    if (core_id < N_COL * nPE) {
      mempool_start_benchmark();
      mempool_cholesky_schedule_q32s(In_matrix, LL_matrix, N, N_ROW, N_COL);
      mempool_linearsolver_q32s(In_matrix, LL_matrix, In, N, N_ROW, N_COL);
      mempool_stop_benchmark();
    }
  }
  mempool_barrier(num_cores);

#endif
#endif

  return 0;
}
