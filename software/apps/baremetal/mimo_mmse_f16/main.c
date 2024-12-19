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

#include "data_mimo_mmse_f16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_cholesky_f16s.h"
#include "baremetal/mempool_linearsolver_f16s.h"
#include "baremetal/mempool_mimo_mmse_f16s.h"

/*
======================
Parameters and defines

DOUBLE_BUFFERING: When defined benchmark double buffered MIMO-MMSE, including
L2-L1 transfers.

For MIMO-MMSE without L2-L1 transfers:
PARALLEL: When defined benchmark parallel MIMO-MMSE.
SINGLE: When defined benchmark single-core MIMO-MMSE.
VEC: When defined benchmark SIMD-vectorized kernels.
ZF: When defined 1 use zero forcing detector.
FOLD: When defined 1 fold matrices in memory.

For MIMO-MMSE with L2-L1 transfers:
DMA_TRANSFER1: When defined transfer inputs for next round at the beginning of
computation. DMA_TRANSFER2: When defined transfer inputs for next round after
Hermitian computation. N_ROUNDS: Define number of rounds of Double-Buffering.
*/

#define ZF (0)
#define FOLD (1)
#define PARALLEL
#define VEC

#ifndef DOUBLE_BUFFERING

/**********************************************************
 **********************************************************
  _   _  ___        _____                     __
 | \ | |/ _ \      |_   _| __ __ _ _ __  ___ / _|
 |  \| | | | |_____  | || '__/ _` | '_ \/ __| |_
 | |\  | |_| |_____  | || | | (_| | | | \__ \  _|
 |_| \_|\___/        |_||_|  \__,_|_| |_|___/_|(_)

***********************************************************
***********************************************************/

#if FOLD
#define NUM_ROW (1 + ((N_ITR * N_TX - 1) / NUM_BANKS))
#define NUM_COL (NUM_BANKS / N_TX)

__fp16 l1_G[2 * N_TX * NUM_BANKS * NUM_ROW]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_L[2 * N_TX * NUM_BANKS * NUM_ROW]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#else
__fp16 l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
#endif

__fp16 l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
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
  uint32_t time_init, time_end;

  /* Initialize matrices */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_H, l2_H, 2 * N_TX * N_RX * N_ITR * sizeof(int16_t));
    dma_memcpy_blocking(l1_y, l2_y, 2 * N_RX * N_ITR * sizeof(int16_t));
    dma_memcpy_blocking(l1_S, l2_S, 2 * N_TX * N_ITR * sizeof(int16_t));
    printf("Data transferred\n");
  }
  mempool_barrier(num_cores);

#ifdef SINGLE
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    time_init = mempool_get_timer();
    for (uint32_t itr = 0; itr < N_ITR; itr++) {
      __fp16 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
      __fp16 *Ptry = l1_y + itr * (2 * N_RX);
      __fp16 *PtrS = l1_S + itr * (2 * N_TX);
      __fp16 *PtrG = l1_G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = l1_L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
#ifdef VEC
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX, 0);
#else
      mempool_hermitian_f16s(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD);
      mempool_MVP_conjtransp_f16s(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16s(PtrG, PtrL, N_TX, 0);
#endif
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX, 0, FOLD);
      mempool_Ltrisol_f16s(PtrL, Ptry3, Ptrx, N_TX, 1, FOLD);
    }
    time_end = mempool_get_timer();
    mempool_stop_benchmark();
  }
#endif

#ifdef PARALLEL
  mempool_start_benchmark();
  time_init = mempool_get_timer();
  // Parallel subcarrier loop
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    __fp16 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    __fp16 *Ptry = l1_y + itr * (2 * N_RX);
    __fp16 *PtrS = l1_S + itr * (2 * N_TX);
    // Auxiliary vectors
#if FOLD
    __fp16 *PtrG = l1_G + (itr / NUM_COL) * (2 * N_TX * NUM_BANKS) +
                   (itr % NUM_COL) * (2 * N_TX);
    __fp16 *PtrL = l1_L + (itr / NUM_COL) * (2 * N_TX * NUM_BANKS) +
                   (itr % NUM_COL) * (2 * N_TX);
    __fp16 *Ptry2 =
        y2 + (itr / NUM_COL) * (2 * NUM_BANKS) + (itr % NUM_COL) * (2 * N_TX);
    __fp16 *Ptry3 =
        y3 + (itr / NUM_COL) * (2 * NUM_BANKS) + (itr % NUM_COL) * (2 * N_TX);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
#else
    __fp16 *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    __fp16 *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
    __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
#endif

#ifdef VEC
    mempool_hermitian_f16vecs(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD);
    mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f16vecs(PtrG, PtrL, N_TX, FOLD);
#else
    mempool_hermitian_f16s(PtrH, PtrG, PtrS, N_RX, N_TX, ZF, FOLD);
    mempool_MVP_conjtransp_f16s(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f16s(PtrG, PtrL, N_TX, FOLD);
#endif
    mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX, 0, FOLD);
    mempool_Ltrisol_f16s(PtrL, Ptry3, Ptrx, N_TX, 1, FOLD);
  }
  mempool_barrier(num_cores);
  time_end = mempool_get_timer();
  mempool_stop_benchmark();
#endif

  if (core_id == 0) {
    printf("Runtime: %d\n", time_end - time_init);
  }
  mempool_check_f16(l1_x, l2_x, 2 * N_RX * N_TX, 0.01f, 0);
  mempool_barrier(num_cores);

  return 0;
}

#else

/**********************************************************
 **********************************************************
  ____  __  __    _       _____                     __
 |  _ \|  \/  |  / \     |_   _| __ __ _ _ __  ___ / _|
 | | | | |\/| | / _ \ _____| || '__/ _` | '_ \/ __| |_
 | |_| | |  | |/ ___ \_____| || | | (_| | | | \__ \  _|
 |____/|_|  |_/_/   \_\    |_||_|  \__,_|_| |_|___/_|(_)

***********************************************************
***********************************************************/

// Inputs-Outputs even double-buffering rounds
__fp16 l1A_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1A_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1A_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1A_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
// Inputs-Outputs odd double-buffering rounds
__fp16 l1B_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1B_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1B_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1B_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
/* Barrier for double buffering */
uint32_t volatile dma_barrier __attribute__((section(".l1")));

// Auxiliary vectors
__fp16 G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1A_H, l2_H, N_TX * N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
    dma_memcpy_blocking(l1A_S, l2_S, N_TX * N_ITR * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  for (uint32_t round = 0; round < N_ROUNDS; round++) {
    /* Start DMA-transfer round */
    mempool_start_benchmark();
    // Transfer vectors
    __fp16 *trsf_H = ((round % 2) == 1) ? l1A_H : l1B_H;
    __fp16 *trsf_y = ((round % 2) == 1) ? l1A_y : l1B_y;
    __fp16 *trsf_S = ((round % 2) == 1) ? l1A_S : l1B_S;
    // Compute vectors
    __fp16 *cmpt_H = ((round % 2) == 0) ? l1A_H : l1B_H;
    __fp16 *cmpt_y = ((round % 2) == 0) ? l1A_y : l1B_y;
    __fp16 *cmpt_S = ((round % 2) == 0) ? l1A_S : l1B_S;
    // On even rounds transfer the result of odd computation and viceversa
    __fp16 *trsf_x = ((round % 2) == 0) ? l1A_x : l1B_x;
    __fp16 *cmpt_x = ((round % 2) == 1) ? l1A_x : l1B_x;

    /*****************************
     *****************************
       ___   _   ___ ___   _   _
      / __| /_\ / __| __| / | (_)
     | (__ / _ \\__ \ _|  | |  _
      \___/_/ \_\___/___| |_| (_)

    ******************************
    ******************************/

#ifdef DMA_TRANSFER1
    // TRANSFER
    if (core_id == 0) {
      dma_barrier = 0;
      dma_memcpy_nonblocking(trsf_H, l2_H,
                             N_TX * N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_S, l2_S, N_TX * N_ITR * sizeof(int32_t));
      if (round >= 1) // Transfer to L2 is done only if not the first round
        dma_memcpy_nonblocking(l2_x, trsf_x, (N_TX * N_ITR) * sizeof(int32_t));
    }
    // COMPUTE
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *PtrH = cmpt_H + itr * (2 * N_TX * N_RX);
      __fp16 *Ptry = cmpt_y + itr * (2 * N_RX);
      __fp16 *Ptrx = cmpt_x + itr * (2 * N_TX);
      __fp16 *PtrS = cmpt_S + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrS, N_RX, N_TX, 0, ZF);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX, 0);
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX, 0, 0);
      mempool_Ltrisol_f16s(PtrL, Ptry3, Ptrx, N_TX, 1, 0);
    }
#endif

    /*****************************
     *****************************
       ___   _   ___ ___   ___   _
      / __| /_\ / __| __| |_  ) (_)
     | (__ / _ \\__ \ _|   / /   _
      \___/_/ \_\___/___| /___| (_)

    ******************************
    ******************************/

#ifdef DMA_TRANSFER2
    // COMPUTE
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *PtrH = cmpt_H + itr * (2 * N_TX * N_RX);
      __fp16 *Ptry = cmpt_y + itr * (2 * N_RX);
      __fp16 *PtrS = cmpt_S + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      mempool_hermitian_f16vecs(PtrH, PtrG, PtrS, N_RX, N_TX, 0, ZF);
      mempool_MVP_conjtransp_f16vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
    }
    mempool_log_barrier(2, core_id);
    // TRANSFER
    mempool_start_benchmark();
    if (core_id == 0) {
      dma_memcpy_nonblocking(trsf_H, l2_H,
                             N_TX * N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_y, l2_y, N_RX * N_ITR * sizeof(int32_t));
      dma_memcpy_nonblocking(trsf_S, l2_S, N_TX * N_ITR * sizeof(int32_t));
      if (round >= 1) // Transfer to L2 is done only if not the
        dma_memcpy_nonblocking(l2_x, trsf_x, (N_TX * N_ITR) * sizeof(int32_t));
    }
    // COMPUTE
    mempool_start_benchmark();
    for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
      __fp16 *Ptrx = cmpt_x + itr * (2 * N_TX);
      __fp16 *PtrG = G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX, 0);
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX, 0, 0);
      mempool_Ltrisol_f16s(PtrL, Ptry3, Ptrx, N_TX, 1, 0);
    }
#endif

    // Synchronize and wait DMA
    if ((num_cores - 1) ==
        __atomic_fetch_add(&dma_barrier, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&dma_barrier, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      dma_wait();
      wake_up_all();
    }
    mempool_wfi();
    mempool_stop_benchmark();
    /* End DMA-transfer round */
  }
  mempool_barrier(num_cores);
  return 0;
}

#endif
