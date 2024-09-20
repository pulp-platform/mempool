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
#include "baremetal/mempool_cholesky_f8s.h"
#include "baremetal/mempool_linearsolver_f16s.h"
#include "baremetal/mempool_linearsolver_f8s.h"
#include "baremetal/mempool_mimo_mmse_f8s.h"

#include "data_mimo_mmse_f8.h"
#define ZF (0) // When asserted use zero-forcing
#define NUM_BANKS (BANKING_FACTOR * NUM_CORES)

__fp8 l1_H[2 * N_TX * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp8 l1_S[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp8 l1_y[2 * N_RX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

__fp16 l1_G[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_L[2 * N_TX * N_TX * N_ITR]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 y2[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 y3[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));
__fp16 l1_x[2 * N_TX * N_ITR]
    __attribute__((aligned(sizeof(int32_t)), section(".l1")));

// Driver program
int main() {

  uint32_t core_id = mempool_get_core_id();
#ifndef BANSHEE
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
#endif

  /* Initialize matrices */
  if (core_id == 0) {
#ifdef BANSHEE
    for (uint32_t i = 0; i < 2 * N_RX * N_TX * N_ITR; i++) {
      l1_H[i] = l2_H[i];
    }
    for (uint32_t i = 0; i < 2 * N_RX * N_ITR; i++) {
      l1_y[i] = l2_y[i];
    }
    for (uint32_t i = 0; i < 2 * N_TX * N_ITR; i++) {
      l1_S[i] = l2_S[i];
    }
#else
    dma_memcpy_blocking(l1_H, l2_H, 2 * N_TX * N_RX * N_ITR * sizeof(int8_t));
    dma_memcpy_blocking(l1_y, l2_y, 2 * N_RX * N_ITR * sizeof(int8_t));
    dma_memcpy_blocking(l1_S, l2_S, 2 * N_TX * N_ITR * sizeof(int16_t));
#endif
    printf("Data transferred\n");
  }
#ifndef BANSHEE
  mempool_barrier(num_cores);
#endif

#ifdef SINGLE
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    for (uint32_t itr = 0; itr < N_ITR; itr++) {
      // 8b inputs
      __fp8 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
      __fp8 *Ptry = l1_y + itr * (2 * N_RX);
      __fp8 *PtrS = l1_S + itr * (2 * N_TX);
      // 16b intermediates and outputs
      __fp16 *PtrG = l1_G + itr * (2 * N_TX * N_TX);
      __fp16 *PtrL = l1_L + itr * (2 * N_TX * N_TX);
      __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
      __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
      __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
      // 8b
#ifdef VEC
      mempool_hermitian_f8vecs(PtrH, PtrS, PtrG, N_RX, N_TX, ZF);
      mempool_MVP_conjtransp_f8vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16vecs(PtrG, PtrL, N_TX);
#else
      mempool_hermitian_f8s(PtrH, PtrS, PtrG, N_RX, N_TX, ZF);
      mempool_MVP_conjtransp_f8s(PtrH, Ptry, Ptry2, N_RX, N_TX);
      mempool_cholesky_f16s(PtrG, PtrL, N_TX);
#endif
      // 16b
      mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX);
      mempool_Lttrisol_f16s(PtrL, Ptry3, Ptrx, N_TX);
    }
    mempool_stop_benchmark();
  }
#endif

#ifdef PARALLEL
  mempool_start_benchmark();
  // Parallel subcarrier loop
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    __fp8 *PtrH = l1_H + itr * (2 * N_TX * N_RX);
    __fp8 *Ptry = l1_y + itr * (2 * N_RX);
    __fp8 *PtrS = l1_S + itr * (2 * N_TX);
    // Auxiliary vectors
    __fp16 *PtrG = l1_G + itr * (2 * N_TX * N_TX);
    __fp16 *PtrL = l1_L + itr * (2 * N_TX * N_TX);
    __fp16 *Ptry2 = y2 + itr * (2 * N_TX);
    __fp16 *Ptry3 = y3 + itr * (2 * N_TX);
    __fp16 *Ptrx = l1_x + itr * (2 * N_TX);
#ifdef VEC
    mempool_hermitian_f8vecs(PtrH, PtrS, PtrG, N_RX, N_TX, ZF);
    mempool_MVP_conjtransp_f8vecs(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f16vecs(PtrG, PtrL, N_TX);
#else
    mempool_hermitian_f8s(PtrH, PtrS, PtrG, N_RX, N_TX, ZF);
    mempool_MVP_conjtransp_f8s(PtrH, Ptry, Ptry2, N_RX, N_TX);
    mempool_cholesky_f16s(PtrG, PtrL, N_TX);
#endif
    // 16b
    mempool_Ltrisol_f16s(PtrL, Ptry2, Ptry3, N_TX);
    mempool_Lttrisol_f16s(PtrL, Ptry3, Ptrx, N_TX);
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#ifdef BANSHEE
  // Check the result
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * N_TX * N_ITR; i++) {
      uint32_t x = (*(uint32_t *)&l1_x[i]) & 0x0000FFFF;
      printf("RES=%04x\n", x);
    }
  }
#else
  mempool_barrier(num_cores);
#endif

  return 0;
}
