// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <math.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_cholesky_f16s.h"
#include "baremetal/mempool_linearsolver_f16s.h"
#include "baremetal/mempool_mimo_mmse_f16s.h"

#include "data_mimo_mmse_f16.h"

// #define DOUBLE_BUFFERING
// #define N_ROUNDS (1)
// #define DMA_TRANSFER2

#ifndef DOUBLE_BUFFERING

/**********************************************/
/* TEST OF THE KERNELS WITH NO DATA MOVEMENTS */
/**********************************************/

//#define SINGLE
#define PARALLEL
//#define FOLDED

__fp16 l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));

uint32_t l1_beamgroups[N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1_Sigma[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_beamgroups, l2_beamgroups, N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1_H, l2_H, N_TX * N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1_Sigma, l2_Sigma, N_TX * N_ITR * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  /* Benchmark */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f16s(l1_H, l1_G, l1_Sigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f16s(l1_H, l1_y, y2, N_RX, N_TX, 0);
    mempool_cholesky_f16vecs(l1_G, l1_L, N_TX);
    mempool_Ltrisol_f16s(l1_L, y2, y3, N_TX);
    mempool_Lttrisol_f16s(l1_L, y3, l1_x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
#endif

#ifdef PARALLEL
  // Each iteration is assigned to a processor
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    uint32_t N_bg = l1_beamgroups[itr];
    uint32_t N_TX_bg = N_TX / N_bg;

    __fp16 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    __fp16 *Ptry = l1_y + itr * (2 * N_RX);
    __fp16 *PtrSigma = l1_Sigma + itr * (2 * N_TX);

    __fp16 *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    __fp16 *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
    __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);

    for (uint32_t itr_bg = 0; itr_bg < N_bg; itr_bg++) {
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrSigma, N_RX, N_TX_bg);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX_bg);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX_bg);
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX_bg);
      mempool_Lttrisol_f16s(PtrL, Ptry3, Ptrx, N_TX_bg);

      // Shift over the subsequent beamgroup
      PtrH += 2 * itr_bg * N_TX_bg * N_RX;
      PtrSigma += 2 * itr_bg * N_TX_bg;
      Ptrx += 2 * itr_bg * N_TX_bg;
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#ifdef FOLDED
  // Each iteration is assigned to a processor
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    __fp16 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    __fp16 *Ptry = l1_y + itr * (2 * N_RX);
    __fp16 *PtrSigma = l1_Sigma + itr * (2 * N_TX);

    __fp16 *PtrG = l1_G + (itr % num_cores) * (2 * N_TX) +
                   (itr / num_cores) * (N_TX * N_BANKS);
    __fp16 *PtrL = l1_L + (itr % num_cores) * (2 * N_TX) +
                   (itr / num_cores) * (N_TX * N_BANKS);
    __fp16 *Ptry2 =
        y2 + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_BANKS);
    __fp16 *Ptry3 =
        y3 + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_BANKS);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);

    mempool_hermitian_f16s(PtrH, PtrG, PtrSigma, N_RX, N_TX, 1, 0);
    mempool_MVP_conjtransp_f16s(PtrH, Ptry, Ptry2, N_RX, N_TX, 1);
    mempool_cholesky_folded_f16s(PtrG, PtrL, N_TX);
    mempool_Ltrisol_folded_f16s(PtrL, Ptry2, Ptry3, N_TX);
    mempool_Lttrisol_folded_f16s(PtrL, Ptry3, Ptrx, N_TX);
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  // Check the result
  mempool_check_f16(l1_x, l2_x, 2 * N_TX, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}

#else

/*******************************************/
/* TEST OF THE KERNELS WITH DATA MOVEMENTS */
/*******************************************/

// Inputs-Outputs even double-buffering rounds
__fp16 l1A_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1A_Sigma[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1A_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1A_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Inputs-Outputs odd double-buffering rounds
__fp16 l1B_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 l1B_Sigma[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1B_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1B_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Auxiliary vectors
__fp16 G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(BANKING_FACTOR * NUM_CORES * sizeof(int32_t)),
                   section(".l1_prio")));
__fp16 y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize

#ifdef DMA_TRANSFER1

  // INITIALIZATION
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1A_H, l2_H, N_TX * N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_Sigma, l2_Sigma, N_TX * N_ITR * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  for (uint32_t round = 0; round < N_ROUNDS; round++) {

    // TRANSFER
    mempool_start_benchmark();
    // Transfer vectors
    __fp16 *trsf_H = ((round % 2) == 1) ? l1A_H : l1B_H;
    __fp16 *trsf_y = ((round % 2) == 1) ? l1A_y : l1B_y;
    __fp16 *trsf_Sigma = ((round % 2) == 1) ? l1A_Sigma : l1B_Sigma;
    // Compute vectors
    __fp16 *cmpt_H = ((round % 2) == 0) ? l1A_H : l1B_H;
    __fp16 *cmpt_y = ((round % 2) == 0) ? l1A_y : l1B_y;
    __fp16 *cmpt_Sigma = ((round % 2) == 0) ? l1A_Sigma : l1B_Sigma;
    // On even rounds we transfer the result of odd computation and viceversa
    __fp16 *trsf_x = ((round % 2) == 0) ? l1A_x : l1B_x;
    __fp16 *cmpt_x = ((round % 2) == 1) ? l1A_x : l1B_x;
    if (core_id == 0) {
      dma_memcpy_nonblocking(trsf_H, l2_H,
                             N_TX * N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_Sigma, l2_Sigma,
                             N_TX * N_ITR * sizeof(int32_t));
      if (round >= 1) // Transfer to L2 is done only if not the
        dma_memcpy_nonblocking(l2_x, trsf_x, (N_TX * N_ITR) * sizeof(int32_t));
    }

    // COMPUTATION
    // Each iteration is assigned to a processor
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *PtrH = cmpt_H + itr * (2 * N_TX * N_RX);
      __fp16 *Ptry = cmpt_y + itr * (2 * N_RX);
      __fp16 *Ptrx = cmpt_x + itr * (2 * N_TX);
      __fp16 *PtrSigma = cmpt_Sigma + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrSigma, N_RX, N_TX);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX);
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX);
      mempool_Lttrisol_f16s(PtrL, Ptry3, Ptrx, N_TX);
    }
    mempool_log_barrier(2, core_id);

    // WAIT FOR DMA
    mempool_start_benchmark();
    dma_wait(); // Wait for the end of the dma transfer
    mempool_stop_benchmark();
  }

#endif

#ifdef DMA_TRANSFER2

  // INITIALIZATION
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1A_H, l2_H, N_TX * N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_Sigma, l2_Sigma, N_TX * N_ITR * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  for (uint32_t round = 0; round < N_ROUNDS; round++) {

    // Transfer vectors
    __fp16 *trsf_H = ((round % 2) == 1) ? l1A_H : l1B_H;
    __fp16 *trsf_y = ((round % 2) == 1) ? l1A_y : l1B_y;
    __fp16 *trsf_Sigma = ((round % 2) == 1) ? l1A_Sigma : l1B_Sigma;
    // Compute vectors
    __fp16 *cmpt_H = ((round % 2) == 0) ? l1A_H : l1B_H;
    __fp16 *cmpt_y = ((round % 2) == 0) ? l1A_y : l1B_y;
    __fp16 *cmpt_Sigma = ((round % 2) == 0) ? l1A_Sigma : l1B_Sigma;
    // On even rounds we transfer the result of odd computation and viceversa
    __fp16 *trsf_x = ((round % 2) == 0) ? l1A_x : l1B_x;
    __fp16 *cmpt_x = ((round % 2) == 1) ? l1A_x : l1B_x;

    // COMPUTATION
    // Each iteration is assigned to a processor
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *PtrH = cmpt_H + itr * (2 * N_TX * N_RX);
      __fp16 *Ptry = cmpt_y + itr * (2 * N_RX);
      __fp16 *PtrSigma = cmpt_Sigma + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrSigma, N_RX, N_TX);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
    }
    mempool_log_barrier(2, core_id);

    // TRANSFER
    mempool_start_benchmark();
    if (core_id == 0) {
      dma_memcpy_nonblocking(trsf_H, l2_H,
                             N_TX * N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_Sigma, l2_Sigma,
                             N_TX * N_ITR * sizeof(int32_t));
      if (round >= 1) // Transfer to L2 is done only if not the
        dma_memcpy_nonblocking(l2_x, trsf_x, (N_TX * N_ITR) * sizeof(int32_t));
    }

    // COMPUTATION
    // Each iteration is assigned to a processor
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *Ptrx = cmpt_x + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX);
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX);
      mempool_Lttrisol_f16s(PtrL, Ptry3, Ptrx, N_TX);
    }
    mempool_log_barrier(2, core_id);

    // WAIT FOR DMA
    mempool_start_benchmark();
    dma_wait(); // Wait for the end of the dma transfer
    mempool_stop_benchmark();
  }

#endif

  mempool_barrier(num_cores);
  return 0;
}

#endif
