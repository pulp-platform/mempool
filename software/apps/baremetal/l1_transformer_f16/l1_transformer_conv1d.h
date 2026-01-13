// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_conv1d_f16.h"
#include "baremetal/mempool_layernorm_f16.h"

/**
  @brief         Computes a 1D convolution using im2col and GEMM.
  @details       Applies a temporal convolution over the input sequence.
                 When RedMule accelerators are available, im2col and GEMM are
  overlapped for improved performance. Otherwise, a core-only im2col + matmul
  implementation is used.
  @param[in]     X         Input tensor, size: [Batch][ChInp][tdSamples]
  @param[in]     F         Filter tensor, size: [Co][Ci][Wf]
  @param[in]     b         Bias vector, size: [Co]
  @param[out]    Y         Output tensor, size: [Batch][Co][tdSamples]
  @param[in]     Batch     Batch size
  @param[in]     ChInp     Number of input channels
  @param[in]     ChOut   Number of output channels
  @param[in]     tdSamples Number of temporal samples per Batch
  @param[in]     Wf        Convolution kernel width
  @return        none
*/

void conv1d(__fp16 const *__restrict__ X, __fp16 const *__restrict__ F,
            __fp16 const *__restrict__ b, __fp16 *__restrict__ Y,
            uint32_t ChInp, uint32_t ChOut, uint32_t Wf, uint32_t Batch,
            uint32_t tdSamples) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  static __fp16 *T = l1_T3; // Should be allocated dinamically

  // Compute
#if NUM_REDMULE_TILES > 0

  // IM2COL Transformation
  const uint32_t pad = Wf / 2;
  const uint32_t rows_per_batch = ChInp * Wf;
  for (uint32_t i = core_id; i < Batch * ChInp * Wf; i += num_cores) {
    uint32_t b = i / rows_per_batch;
    uint32_t r = i % rows_per_batch;
    uint32_t j = r / Wf;
    uint32_t f = r % Wf;

    uint32_t t_base = i * tdSamples;
    uint32_t x_base = b * (ChInp * tdSamples) + j * tdSamples;

    for (uint32_t k = 0; k < tdSamples; k++) {
      int32_t idx = (int32_t)k - (int32_t)pad + (int32_t)f;
      if (idx >= 0 && idx < (int32_t)tdSamples) {
        T[t_base + j] = X[x_base + (uint32_t)idx];
      } else {
        T[t_base + j] = 0;
      }
    }
  }
  mempool_barrier(num_cores);

  // GEMM
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(F);
      unsigned int W_ptr = (unsigned int)(&T[i * ChInp * tdSamples * Wf]);
      unsigned int O_ptr = (unsigned int)(&Y[i * ChOut * tdSamples]);
      uint16_t M = (uint16_t)(ChOut);
      uint16_t N = (uint16_t)(ChInp * Wf);
      uint16_t P = (uint16_t)(tdSamples);
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);

#else
  for (uint32_t i = core_id; i < Batch; i += num_cores) {
    __fp16 *X_ptr = &X[i * ChInp * tdSamples];
    __fp16 *Y_ptr = &Y[i * ChOut * tdSamples];
    __fp16 *T_ptr = &T[i * ChInp * tdSamples * Wf];
    conv1d_im2col_matmul_f16(X_ptr, F, b, T_ptr, Y_ptr, ChInp, ChOut, tdSamples,
                             Wf);
  }
  // Synchronize
  mempool_barrier(num_cores);
#endif

  return;
}

/**
  @brief         Layer normalization followed by 1D convolution.
  @details       This function performs a fused operation consisting of:
                 1) DMA transfer of convolution weights and biases from L2
                    memory to L1 memory.
                 2) Layer normalization of the input tensor, parallelized
                    across cores and Batches.
                 3) A 1D temporal convolution using the normalized output as
                    input.

                 The convolution stage internally uses the `conv1d` function,
                 which may leverage RedMule accelerators if available.
                 Synchronization barriers ensure correctness between DMA,
                 normalization, and convolution phases.

  @param[in]     l2_F      Pointer to filter weights in L2 memory,
                           shape [ChOut][ChInp][Wf]
  @param[in]     l2_b      Pointer to bias vector in L2 memory,
                           shape [ChOut]
  @param[in]     I         Input tensor in L1 memory,
                           shape [Batch][ChInp][tdSamples]
  @param[out]    O         Output tensor in L1 memory,
                           shape [Batch][ChOut][tdSamples]
  @param[in]     Batch     Batch size
  @param[in]     ChInp     Number of input channels
  @param[in]     ChOut     Number of output channels
  @param[in]     tdSamples Number of temporal samples per Batch
  @param[in]     Wf        Convolution kernel width
  @return        None
*/

void *layernorm_conv1d(__fp16 const *__restrict__ l2_F,
                       __fp16 const *__restrict__ l2_b, __fp16 *__restrict__ I,
                       __fp16 *__restrict__ O, uint32_t Batch, uint32_t ChInp,
                       uint32_t ChOut, uint32_t tdSamples, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  static __fp16 *F = l1_F; // Should be allocated dinamically
  static __fp16 *b = l1_b; // Should be allocated dinamically
  if (core_id == 0) {
    dma_memcpy_nonblocking(F, l2_F, ChOut * ChInp * Wf * sizeof(int16_t));
    dma_memcpy_nonblocking(b, l2_b, ChOut * sizeof(int16_t));
  }

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transfer weights                                */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Compute layer normalization                                            */
  /**************************************************************************/

  if (num_cores < Batch) {
    if (core_id == 0) {
      printf("ERROR: attention_td requires num_cores (%u) >= Batch (%u)\n",
             num_cores, Batch);
    }
    mempool_barrier(num_cores);
    return NULL;
  }

#if defined(COMPUTE)
  mempool_start_benchmark();
  static __fp16 *T1 = l1_T1; // Should be allocated dinamically
  uint32_t num_cores_per_batch = num_cores / Batch;
  uint32_t batch_id = core_id % num_cores_per_batch;
  uint32_t idx = core_id / num_cores_per_batch;
  __fp16 *X_ptr = &I[idx * ChInp * tdSamples];
  __fp16 *Y_ptr = &T1[idx * ChInp * tdSamples];
  layernorm_parallel_2x4_f16vec(X_ptr, Y_ptr, ChInp, tdSamples, batch_id,
                                num_cores_per_batch);
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Compute layer normalization                     */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Synchronize and wait for weights transfer end                          */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_wait();
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Synchronize and wait for weights transfer end   */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Compute convolution                                                    */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  conv1d(T1, F, b, O, ChInp, ChOut, Wf, Batch, tdSamples);
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Compute convolution                             */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  return O;
}
