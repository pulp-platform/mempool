// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_conv2d_f16.h"
#include "baremetal/mempool_layernorm_f16.h"

/*
                matrix_M                         matrix_M
           +----------------+ m             +----------------+ k
 matrix_N /|               /| a   matrix_N /|               /| e
         / |              / | t           / |              / | r
        +----------------+  | r          +----------------+  | n
        |  |             |  | i          |  |             |  | e
        |  |   Sinp      |  | x    ===>  |  |   Sout      |  | l
        |  +-------------|--+ D          |  +-------------|--+ D
        | /              | /             | /              | /
        |/               |/              |/               |/
        +----------------+               +----------------+
*/

void cnn_state_block(__fp16 *__restrict__ Sinp, __fp16 *__restrict__ Stmp,
                     __fp16 *__restrict__ Sout, __fp16 *__restrict__ Wdw,
                     __fp16 *__restrict__ Wpw, uint32_t matrix_M,
                     uint32_t matrix_N, uint32_t matrix_D, uint32_t kernel_K,
                     uint32_t kernel_D, uint32_t do_norm, uint32_t do_relu) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Separable Convolution
  conv2d_depthwise_f16(Sinp, Stmp, Wdw, matrix_M, matrix_N, matrix_D, kernel_K);
  conv2d_pointwise_f16(Stmp, Sout, Wpw, matrix_M, matrix_N, matrix_D, kernel_D);
  mempool_barrier(num_cores);

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Conv2D (Depthwise/Pointwise)                    */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  // Layer Normalization
  if (do_norm) {
    layernorm_parallel_2x4_f16vec(Sout, Stmp, matrix_M * matrix_N, kernel_D,
                                  core_id, num_cores);
    mempool_barrier(num_cores);
  }

  // ReLU
  if (do_relu) {
    for (uint32_t i = core_id * 2 * BANKING_FACTOR;
         i < matrix_M * matrix_N * matrix_D;
         i += num_cores * 2 * BANKING_FACTOR) {
      for (uint32_t j = 0; j < 2 * BANKING_FACTOR; j++) {
        bool isless = false;
        asm volatile("fle.h %[b], %[s1], zero;"
                     : [s2] "+&r"(Sout[i + j])
                     : [s1] "r"(Stmp[i + j]), [b] "r"(isless)
                     :);
        Sout[i + j] = isless ? Stmp[i + j] : (__fp16)0.0f;
      }
    }
    mempool_barrier(num_cores);
  }

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: LayerNorm and ReLU                              */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  return;
}

void cnn_state_update(__fp16 *__restrict__ l2_St1, __fp16 *__restrict__ l2_Wdw,
                      __fp16 *__restrict__ l2_Wpw, uint32_t matrix_M,
                      uint32_t matrix_N, uint32_t matrix_D, uint32_t kernel_K,
                      uint32_t kernel_D) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  static __fp16 *S1 = l1_St1;  // Should be allocated dinamically
  static __fp16 *S2 = l1_St2;  // Should be allocated dinamically
  static __fp16 *T1 = l1_T1;   // Should be allocated dinamically
  static __fp16 *T2 = l1_T2;   // Should be allocated dinamically
  static __fp16 *Wdw = l1_Wdw; // Should be allocated dinamically
  static __fp16 *Wpw = l1_Wpw; // Should be allocated dinamically

  if (core_id == 0) {
    dma_memcpy_blocking(
        S1, l2_St1, NF * NS * (NRX * 2 + 2 + NRX + 2 * NRX) * sizeof(int16_t));
    dma_memcpy_blocking(Wdw, l2_Wdw,
                        matrix_D * kernel_K * kernel_K * sizeof(int16_t));
    dma_memcpy_blocking(Wpw, l2_Wpw, matrix_D * kernel_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  cnn_state_block(S1, T1, S2, Wdw, Wpw, matrix_M, matrix_N, matrix_D, kernel_K,
                  kernel_D, 1, 1);

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: First CNN Block                                 */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  if (core_id == 0) {
    dma_memcpy_blocking(Wdw, l2_Wdw,
                        kernel_D * kernel_K * kernel_K * sizeof(int16_t));
    dma_memcpy_blocking(Wpw, l2_Wpw, kernel_D * kernel_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  cnn_state_block(S2, T1, T2, Wdw, Wpw, matrix_M, matrix_N, kernel_D, kernel_K,
                  kernel_D, 1, 1);

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Second CNN Block                                */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  if (core_id == 0) {
    dma_memcpy_blocking(Wdw, l2_Wdw,
                        kernel_D * kernel_K * kernel_K * sizeof(int16_t));
    dma_memcpy_blocking(Wpw, l2_Wpw, matrix_D * kernel_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  cnn_state_block(T2, T1, S2, Wdw, Wpw, matrix_M, matrix_N, kernel_D, kernel_K,
                  matrix_D, 0, 0);

  // Residual connection: S2 += S1
  for (uint32_t i = core_id * 2 * BANKING_FACTOR;
       i < matrix_M * matrix_N * matrix_D;
       i += num_cores * 2 * BANKING_FACTOR) {
    for (uint32_t j = 0; j < 2 * BANKING_FACTOR; j++) {
      asm volatile("fadd.h %[s2], %[s2], %[s1];"
                   : [s2] "+&r"(S2[i + j])
                   : [s1] "r"(S1[i + j]));
    }
  }
  mempool_barrier(num_cores);

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Third CNN Block                                 */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  return;
}
