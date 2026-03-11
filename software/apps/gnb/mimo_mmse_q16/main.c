// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_mimo_mmse_q16.h"

#include "baremetal/mempool_cholesky_q16s.h"
#include "baremetal/mempool_linearsolver_q16s.h"
#include "baremetal/mempool_mimo_mmse_q16s.h"

/*
======================
Parameters and defines

PARALLEL: When defined benchmark parallel MIMO-MMSE.
SINGLE: When defined benchmark single-core MIMO-MMSE.
FOLD: When defined 1 fold matrices in memory.
*/

#define FOLD (1)
#define PARALLEL

#if FOLD
#define NUM_ROW (1 + ((N_ITR * N_TX - 1) / NUM_BANKS))
#define NUM_COL (NUM_BANKS / N_TX)

int16_t l1_G[2 * N_TX * NUM_BANKS * NUM_ROW]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t l1_L[2 * N_TX * NUM_BANKS * NUM_ROW]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#else
int16_t l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#endif

int16_t l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t l1_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
int16_t l1_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
int16_t y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
int16_t y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
int16_t l1_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  uint32_t time_init, time_end;

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_H, l2_H, N_TX * N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1_S, l2_S, N_TX * N_ITR * sizeof(int32_t));
    printf("Data transferred\n");
  }
  mempool_barrier(num_cores);

  /* Benchmark */
#ifdef SINGLE

  if (core_id == 0) {
    mempool_start_benchmark();
    time_init = mempool_get_timer();
    v2s *PtrH = (v2s *)l1_H;
    v2s *PtrG = (v2s *)l1_G;
    v2s *PtrS = (v2s *)l1_Sigma;
    v2s *Ptry = (v2s *)l1_y;
    v2s *Ptry2 = (v2s *)y2;
    mempool_hermitian_q16vecs(PtrH, PtrG, PtrS, N_RX, N_TX);
    mempool_MVP_conjtransp_q16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX, FOLD);
    mempool_cholesky_q16vecs(l1_G, l1_L, N_TX, FOLD);
    mempool_Ltrisol_q16vecs(l1_L, y2, y3, N_TX, 0, FOLD);
    mempool_Ltrisol_q16vecs(l1_L, y3, l1_x, N_TX, 1, FOLD);
    time_end = mempool_get_timer();
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

#endif

#ifdef PARALLEL

  mempool_start_benchmark();
  time_init = mempool_get_timer();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    int16_t *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    int16_t *Ptry = l1_y + itr * (2 * N_RX);
    int16_t *PtrS = l1_S + itr * (2 * N_TX);

#if FOLD
    int16_t *PtrG = l1_G + (itr / NUM_COL) * (2 * N_TX * NUM_BANKS) +
                    (itr % NUM_COL) * (2 * N_TX);
    int16_t *PtrL = l1_L + (itr / NUM_COL) * (2 * N_TX * NUM_BANKS) +
                    (itr % NUM_COL) * (2 * N_TX);
    int16_t *Ptry2 =
        y2 + (itr / NUM_COL) * (2 * NUM_BANKS) + (itr % NUM_COL) * (2 * N_TX);
    int16_t *Ptry3 =
        y3 + (itr / NUM_COL) * (2 * NUM_BANKS) + (itr % NUM_COL) * (2 * N_TX);
    int16_t *Ptrx = l1_x + itr * (2 * N_TX);
#else
    int16_t *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    int16_t *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    int16_t *Ptry2 = y2 + itr * (2 * N_TX);
    int16_t *Ptry3 = y3 + itr * (2 * N_TX);
    int16_t *Ptrx = l1_x + itr * (2 * N_TX);
#endif

    mempool_hermitian_q16vecs((v2s *)PtrH, (v2s *)PtrG, (v2s *)PtrS, N_RX,
                              N_TX);
    mempool_MVP_conjtransp_q16vecs((v2s *)PtrH, (v2s *)Ptry, (v2s *)Ptry2, N_RX,
                                   N_TX, FOLD);
    mempool_cholesky_q16vecs(PtrG, PtrL, N_TX, FOLD);
    mempool_Ltrisol_q16vecs(PtrL, Ptry2, Ptry3, N_TX, 0, FOLD);
    mempool_Ltrisol_q16vecs(PtrL, Ptry3, Ptrx, N_TX, 1, FOLD);
  }
  mempool_barrier(num_cores);
  time_end = mempool_get_timer();
  mempool_stop_benchmark();

#endif

  if (core_id == 0) {
    printf("Runtime: %d\n", time_end - time_init);
  }
  mempool_barrier(num_cores);

  return 0;
}
