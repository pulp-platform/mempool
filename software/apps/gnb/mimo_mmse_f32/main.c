// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_mimo_mmse_f32.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_mimo_mmse_f32p.h"
#include "baremetal/mempool_mimo_mmse_f32s.h"

#if defined(__XDIVSQRT)
#include "baremetal/mempool_cholesky_f32s.h"
#include "baremetal/mempool_linearsolver_f32s.h"
#endif

/*
======================
Parameters and defines

PARALLEL: When defined benchmark parallel MIMO-MMSE.
SINGLE: When defined benchmark single-core MIMO-MMSE.
ZF: When defined 1 use zero forcing detector.
FOLD: When defined 1 fold matrices in memory.
PARALLEL_HERMITIAN: When defined the Hermitian is finely-grained parallelized
over a group of cores. ZF: When defined 1 use zero forcing detector. FOLD: When
defined 1 fold matrices in memory.
*/

#define ZF (0)
#define FOLD (0)
#define SINGLE

float l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
float l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
float l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
float l1_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
float l1_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

float y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
float y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
float l1_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_H, l2_H, 2 * N_ITR * N_RX * N_TX * sizeof(int32_t));
    dma_memcpy_blocking(l1_y, l2_y, 2 * N_ITR * N_RX * sizeof(int32_t));
    dma_memcpy_blocking(l1_S, l2_S, 2 * N_ITR * N_TX * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

#if defined(SINGLE) && defined(__XDIVSQRT)
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f32s(l1_H, l1_G, l1_S, N_RX, N_TX, ZF, FOLD);
    mempool_MVP_conjtransp_f32s(l1_H, l1_y, y2, N_RX, N_TX);
    mempool_cholesky_f32s(l1_G, l1_L, N_TX, FOLD);
    mempool_Ltrisol_f32s(l1_L, y2, y3, N_TX, 0, FOLD);
    mempool_Ltrisol_f32s(l1_L, y3, l1_x, N_TX, 1, FOLD);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#if defined(PARALLEL) && defined(__XDIVSQRT)

  // Each iteration is assigned to a processor

  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    // Inputs
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *PtrS = l1_S + itr * (2 * N_TX);
    float *Ptry = l1_y + itr * (2 * N_RX);

    // Intermediate results and outputs

#if FOLD
    __fp16 *PtrG = l1_G + (itr % NUM_ROW) * (2 * N_TX * NUM_BANKS) +
                   (itr / NUM_ROW) * (2 * N_TX);
    __fp16 *PtrL = l1_L + (itr % NUM_ROW) * (2 * N_TX * NUM_BANKS) +
                   (itr / NUM_ROW) * (2 * N_TX);
    __fp16 *Ptry2 =
        y2 + (itr % NUM_ROW) * NUM_BANKS + (itr / NUM_ROW) * (2 * N_TX);
    __fp16 *Ptry3 =
        y3 + (itr % NUM_ROW) * NUM_BANKS + (itr / NUM_ROW) * (2 * N_TX);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
#else
    float *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    float *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    float *Ptry2 = y2 + itr * (2 * N_TX);
    float *Ptry3 = y3 + itr * (2 * N_TX);
    float *Ptrx = l1_x + itr * (2 * N_TX);
#endif

    mempool_hermitian_f32s(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD);
    mempool_MVP_conjtransp_f32s(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f32s(PtrG, PtrL, N_TX, FOLD);
    mempool_Ltrisol_f32s(PtrL, Ptry2, Ptry3, N_TX, 0, FOLD);
    mempool_Ltrisol_f32s(PtrL, Ptry3, Ptrx, N_TX, 1, FOLD);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif

#if defined(PARALLEL_HERMITIAN) && defined(__XDIVSQRT)
  mempool_start_benchmark();

  // Each iteration is assigned to a pool of processors
  // In a pool each PE gets a column of the H matrix, accumulating
  // a row of the output matrix

  uint32_t pool_id = core_id / N_TX;
  uint32_t num_pools = num_cores / N_TX;
  for (uint32_t itr = pool_id; itr < N_ITR; itr += num_pools) {
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    float *PtrS = l1_S + itr * N_TX;
    mempool_hermitian_f32p(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD,
                           core_id % N_TX, N_TX);
  }
  mempool_stop_benchmark();

  // Each iteration is assigned to a processor

  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    // Inputs
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *Ptry = l1_y + itr * (2 * N_RX);
    // Intermediate results and outputs
    float *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    float *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    float *Ptry2 = y2 + itr * (2 * N_TX);
    float *Ptry3 = y3 + itr * (2 * N_TX);
    float *Ptrx = l1_x + itr * (2 * N_TX);
    mempool_MVP_conjtransp_f32s(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f32s(PtrG, PtrL, N_TX, 0);
    mempool_Ltrisol_f32s(PtrL, Ptry2, Ptry3, N_TX, 0, FOLD);
    mempool_Ltrisol_f32s(PtrL, Ptry3, Ptrx, N_TX, 1, FOLD);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif

  // Check the result
  mempool_check_f32(l1_x, l2_x, 2 * N_TX, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
