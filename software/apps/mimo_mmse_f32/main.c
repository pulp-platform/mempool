// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data_mimo_mmse_f32.h"
#include "kernel/mempool_checks.h"
#include "kernel/mempool_cholesky_f32s.h"
#include "kernel/mempool_linearsolver_f32s.h"
#include "kernel/mempool_mimo_mmse_f32p.h"
#include "kernel/mempool_mimo_mmse_f32s.h"

//#define SINGLE
//#define JACOBI
#define PARALLEL

float l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
float l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
float l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
float l1_Sigma[N_TX * N_ITR] __attribute__((section(".l1_prio")));

float l1_y[2 * N_RX * N_ITR] __attribute__((section(".l1_prio")));
float y2[2 * N_TX * N_ITR] __attribute__((section(".l1_prio")));
float y3[2 * N_TX * N_ITR] __attribute__((section(".l1_prio")));
float l1_x[2 * N_TX * N_ITR] __attribute__((section(".l1_prio")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_H, l2_H, 2 * N_ITR * N_RX * N_TX * sizeof(int32_t));
    dma_memcpy_blocking(l1_y, l2_y, 2 * N_ITR * N_RX * sizeof(int32_t));
    dma_memcpy_blocking(l1_Sigma, l2_Sigma, N_ITR * N_TX * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

#ifdef SINGLE
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f32s(l1_H, l1_G, l1_Sigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f32s(l1_H, l1_y, y2, N_RX, N_TX, 0);
    mempool_cholesky_f32s(l1_G, l1_L, N_TX);
    mempool_Ltrisol_f32s(l1_L, y2, y3, N_TX);
    mempool_Lttrisol_f32s(l1_L, y3, l1_x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef JACOBI
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f32s(l1_H, l1_G, l1_Sigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f32s(l1_H, l1_y, y2, N_RX, N_TX, 0);
    mempool_stop_benchmark();
    mempool_start_benchmark();
    mempool_jacobi_f32s(l1_G, y2, l1_x, N_TX, 0.005f, 20U);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  // Each iteration is assigned to a processor
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    // Inputs
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *PtrSigma = l1_Sigma + itr * N_TX;
    float *Ptry = l1_y + itr * (2 * N_RX);
    // Intermediate results and outputs
    float *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    float *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    float *Ptry2 = y2 + itr * (2 * N_TX);
    float *Ptry3 = y3 + itr * (2 * N_TX);
    float *Ptrx = l1_x + itr * (2 * N_TX);
    mempool_hermitian_f32s(PtrH, PtrG, PtrSigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f32s(PtrH, Ptry, Ptry2, N_RX, N_TX, 0);
    mempool_cholesky_f32s(PtrG, PtrL, N_TX);
    mempool_Ltrisol_f32s(PtrL, Ptry2, Ptry3, N_TX);
    mempool_Lttrisol_f32s(PtrL, Ptry3, Ptrx, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif

#ifdef PARALLEL_PARALLEL_HERMITIAN
  mempool_start_benchmark();
  // Each iteration is assigned to a pool of processors
  // In a pool each PE gets a column of the H matrix, accumulating a row of the
  // output matrix
  uint32_t pool_id = core_id / N_TX;
  uint32_t num_pools = num_cores / N_TX;
  for (uint32_t itr = pool_id; itr < N_ITR; itr += num_pools) {
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    float *PtrSigma = l1_Sigma + itr * N_TX;
    mempool_hermitian_f32p(PtrH, PtrG, PtrSigma, N_RX, N_TX, 0, 0,
                           core_id % N_TX, N_TX);
  }
  mempool_stop_benchmark();
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
    mempool_MVP_conjtransp_f32s(PtrH, Ptry, Ptry2, N_RX, N_TX, 0);
    mempool_cholesky_f32s(PtrG, PtrL, N_TX);
    mempool_Ltrisol_f32s(PtrL, Ptry2, Ptry3, N_TX);
    mempool_Lttrisol_f32s(PtrL, Ptry3, Ptrx, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif

#ifdef FOLDED
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    // Inputs
    float *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    float *PtrSigma = l1_Sigma + itr * N_TX;
    float *Ptry = l1_y + itr * (2 * N_RX);
    // Intermediate results and outputs
    float *PtrG = l1_G + (itr % num_cores) * N_TX +
                  (itr / num_cores) * (2 * N_TX * N_BANKS);
    float *PtrL = l1_L + (itr % num_cores) * N_TX +
                  (itr / num_cores) * (2 * N_TX * N_BANKS);
    float *Ptry2 =
        y2 + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    float *Ptry3 =
        y3 + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    float *Ptrx =
        l1_x + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    mempool_hermitian_f32s(PtrH, PtrG, PtrSigma, N_RX, N_TX, 1, 0);
    mempool_MVP_conjtransp_f32s(PtrH, Ptry, Ptry2, N_RX, N_TX, 1);
    mempool_cholesky_folded_f32s(PtrG, PtrL, N_TX);
    mempool_Ltrisol_folded_f32s(PtrL, Ptry2, Ptry3, N_TX);
    mempool_Lttrisol_folded_f32s(PtrL, Ptry3, Ptrx, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif

  // Check the result
  mempool_check_f32(l1_x, l2_x, 2 * N_TX, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
