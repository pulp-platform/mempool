// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_matmul_f16.h"
#include "baremetal/mempool_softmax_f16.h"
#include "l1_transformer_conv1d.h"

/**
  @brief         Computes scaled dot-product attention.
  @details       Performs the operation:
                   A = Softmax(Q * Kt) * V
                 independently for each batch.
                 When available, RedMule accelerators are used for GEMM;
                 otherwise a core-only implementation is executed.
  @param[in]     Q         Query tensor, [Batch][SeqLen][tdEmbed]
  @param[in]     Kt        Key tensor (transposed), [Batch][tdEmbed][SeqLen]
  @param[in]     V         Value tensor, [Batch][SeqLen][tdEmbed]
  @param[out]    A         Attention output tensor
  @param[in]     Batch     Number of batches
  @param[in]     SeqLen    Sequence Length
  @param[in]     tdEmbed   Temporal embedding dimension
  @return        none
*/

void attention_block(__fp16 const *__restrict__ Q,
                     __fp16 const *__restrict__ Kt,
                     __fp16 const *__restrict__ V, __fp16 *__restrict__ A,
                     uint32_t Batch, uint32_t SeqLen, uint32_t tdEmbed) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

#if NUM_REDMULE_TILES > 0
  // RedMulE implementation

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  static __fp16 *S = l1_T4;  // Should be allocated dinamically
  static __fp16 *Aw = l1_T5; // Should be allocated dinamically

  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(Q + i * (SeqLen * tdEmbed));
      unsigned int W_ptr = (unsigned int)(Kt + i * (tdEmbed * SeqLen));
      unsigned int O_ptr = (unsigned int)(S + i * (SeqLen * SeqLen));
      uint16_t M = (uint16_t)SeqLen;
      uint16_t N = (uint16_t)tdEmbed;
      uint16_t P = (uint16_t)SeqLen;
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);

  // Softmax
  if (Batch < num_cores) {
    uint32_t num_cores_per_softmax = num_cores / Batch;
    uint32_t softmax_id = core_id % num_cores_per_softmax;
    uint32_t idx = core_id / num_cores_per_softmax;
    softmax_parallel_2x4_f16vec(&S[idx * (SeqLen * SeqLen)],
                                &Aw[idx * (SeqLen * SeqLen)], SeqLen, SeqLen,
                                softmax_id, num_cores_per_softmax);
  } else {
    for (uint32_t i = core_id; i < Batch; i += num_cores) {
      softmax_parallel_2x4_f16vec(&S[i * (SeqLen * SeqLen)],
                                  &Aw[i * (SeqLen * SeqLen)], SeqLen, SeqLen, 0,
                                  1);
    }
  }
  mempool_barrier(num_cores);

  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_cores) {
      unsigned int I_ptr = (unsigned int)(Aw + i * (SeqLen * SeqLen));
      unsigned int W_ptr = (unsigned int)(V + i * (SeqLen * tdEmbed));
      unsigned int O_ptr = (unsigned int)(A + i * (SeqLen * tdEmbed));
      uint16_t M = (uint16_t)SeqLen;
      uint16_t N = (uint16_t)SeqLen;
      uint16_t P = (uint16_t)tdEmbed;
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

  static __fp16 *S = l1_T4;  // Should be allocated dinamically
  static __fp16 *Aw = l1_T5; // Should be allocated dinamically

  // Q*Kt
  for (uint32_t i = 0; i < Batch; i++) {
    matmul_4x2_parallel_f16vec(
        &Q[i * (SeqLen * tdEmbed)], &Kt[i * (tdEmbed * SeqLen)],
        &S[i * (SeqLen * SeqLen)], SeqLen, tdEmbed, SeqLen, core_id, num_cores);
  }
  mempool_barrier(num_cores);

  // Softmax
  for (uint32_t i = 0; i < Batch; i++) {
    softmax_parallel_2x4_f16vec(&S[i * (SeqLen * SeqLen)],
                                &Aw[i * (SeqLen * SeqLen)], SeqLen, SeqLen,
                                core_id, num_cores);
  }
  mempool_barrier(num_cores);

  // A = Softmax(Q*Kt)*V
  for (uint32_t i = 0; i < Batch; i++) {
    matmul_4x2_parallel_f16vec(&Aw[i * (SeqLen * SeqLen)],
                               &V[i * (SeqLen * tdEmbed)],
                               &A[i * (SeqLen * tdEmbed)], SeqLen, SeqLen,
                               tdEmbed, core_id, num_cores);
  }
  mempool_barrier(num_cores);

#endif

  return;
}

typedef enum { EBT = 0, TBE = 1 } permute_mode_t;

/**
  @brief         Permutes and splits Q, K, V tensors from a packed input.
  @details       Converts input layout
                 [Beam][3*Embed][tdSamples]
                 into (depending on input mode):
                    - EBT:
                      Q  : [Embed][Beam][tdSamples]
                      V  : [Embed][Beam][tdSamples]
                      Kt : [Beam][Embed][tdSamples] (transposed for GEMM)
                    - TBE:
                      Q  : [tdSamples][Beam][Embed]
                      V  : [tdSamples][Beam][Embed]
                      Kt : [Beam][tdSamples][Embed] (transposed for GEMM)
                 The work is distributed across mempool cores.
  @param[in]     IN        Packed input tensor containing Q, K, V
  @param[out]    Q         Query tensor
  @param[out]    Kt        Key tensor (transposed)
  @param[out]    V         Value tensor
  @param[in]     Beam      Beam size (sequence length)
  @param[in]     Embed     Embedding dimension
  @param[in]     tdSamples Number of temporal samples
  @return        none
*/

void permute_qkv(__fp16 const *__restrict__ IN, __fp16 *__restrict__ Q,
                 __fp16 *__restrict__ Kt, __fp16 *__restrict__ V, uint32_t Beam,
                 uint32_t Embed, uint32_t tdSamples, permute_mode_t mode) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  for (uint32_t i = core_id; i < Beam; i += num_cores) {
    uint32_t b = i / Embed;
    uint32_t e = i % Embed;
    switch (mode) {
    case TBE:
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t o_idx, o_tidx, i_idx;
        i_idx = (b * (3 * Embed) + e) * tdSamples + t;
        o_idx = (t * Beam + b) * Embed + e;
        o_tidx = (b * tdSamples + t) * Embed + e;
        Q[o_idx] = IN[i_idx];
        Kt[o_tidx] = IN[i_idx + Embed * tdSamples];
        V[o_idx] = IN[i_idx + 2 * Embed * tdSamples];
      }
      break;
    default: // EBT
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t o_idx, o_tidx, i_idx;
        i_idx = (b * (3 * Embed) + e) * tdSamples + t;
        o_idx = (e * Beam + b) * tdSamples + t;
        o_tidx = (b * Embed + e) * tdSamples + t;
        Q[o_idx] = IN[i_idx];
        Kt[o_tidx] = IN[i_idx + Embed * tdSamples];
        V[o_idx] = IN[i_idx + 2 * Embed * tdSamples];
      }
      break;
    }
  }

  return;
}

/**
  @brief         Depending on input mode:
                 - EBT_TO BET:
                   From [Embed][Beam][tdSamples] to [Beam][Embed][tdSamples].
                 - TBE_TO BET:
                   From [tdSamples][Beam][Embed] to [Beam][Embed][tdSamples].
  @details       Used to restore beam-major layout after attention computation.
                 The permutation is parallelized across mempool cores.
  @param[in]     IN        Input tensor
  @param[out]    OUT       Output tensor
  @param[in]     Beam      Beam size
  @param[in]     Embed     Embedding dimension
  @param[in]     tdSamples Number of temporal samples
  @return        none
*/

void permute_result(__fp16 const *__restrict__ IN, __fp16 *__restrict__ OUT,
                    uint32_t Beam, uint32_t Embed, uint32_t tdSamples,
                    permute_mode_t mode) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  for (uint32_t i = core_id; i < Beam * Embed; i += num_cores) {
    uint32_t b = i / Embed;
    uint32_t e = i % Embed;
    switch (mode) {
    case TBE:
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t i_idx, o_idx;
        i_idx = (t * Beam + b) * Embed + e;
        o_idx = (b * Embed + e) * tdSamples + t;
        OUT[o_idx] = IN[i_idx];
      }
      break;
    default: // EBT
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t i_idx, o_idx;
        i_idx = (e * Beam + b) * tdSamples + t;
        o_idx = (b * Embed + e) * tdSamples + t;
        OUT[o_idx] = IN[i_idx];
      }
      break;
    }
  }

  return;
}

/**
  @brief         Computes the full attention block.
  @details       Executes the following pipeline:
                   1. DMA transfer of inputs and weights
                   2. Layer normalization
                   3. 1D convolution for QKV projection
                   4. Attention computation
                 The function exploits mempool cores, DMA engines,
                 and RedMule accelerators when available.
  @param[in]     l2_I      Input tensor in L2 memory
  @param[in]     l2_F      Convolution filter weights in L2 memory
  @param[in]     l2_b      Convolution bias vector in L2 memory
  @param[in]     Beam      Beam size
  @param[in]     Embed     Embedding dimension
  @param[in]     tdSamples Number of temporal samples
  @param[in]     Wf        Dimension convolution
  @param[in]     mode      Attention is executed in the temporal/embed domain.
  @return        Pointer to output tensor (or NULL on error)
*/

void *attention(__fp16 const *__restrict__ l2_I,
                __fp16 const *__restrict__ l2_F,
                __fp16 const *__restrict__ l2_b, uint32_t Beam, uint32_t Embed,
                uint32_t tdSamples, uint32_t Wf, permute_mode_t mode) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  /**************************************************************************/
  /* Transfer inputs                                                        */
  /**************************************************************************/

  mempool_start_benchmark();
  static __fp16 *I = l1_I;   // Should be allocated dinamically
  static __fp16 *T1 = l1_T1; // Should be allocated dinamically
  static __fp16 *T2 = l1_T2; // Should be allocated dinamically
  if (core_id == 0) {
    dma_memcpy_blocking(I, l2_I, Embed * Beam * tdSamples * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#if defined(VERBOSE)
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Transfer inputs                                 */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Conv1D block                                                           */
  /**************************************************************************/

  layernorm_conv1d(l2_F, l2_b, I, T2, Beam, Embed, Embed * 3, tdSamples, Wf);

  /**************************************************************************/
  /* Permute to QKV                                                         */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  static __fp16 *Q;
  static __fp16 *Kt;
  static __fp16 *V;
  Q = &T1[0 * Beam * Embed * tdSamples];
  Kt = &T1[1 * Beam * Embed * tdSamples];
  V = &T1[2 * Beam * Embed * tdSamples];
  permute_qkv(T2, Q, Kt, V, Beam, Embed, tdSamples, mode);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Permute to QKV                                  */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Attention                                                              */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  switch (mode) {
  case TBE:
    attention_block(Q, Kt, V, T2, tdSamples, Beam, Embed);
    break;
  default: // EBT
    attention_block(Q, Kt, V, T2, Embed, Beam, tdSamples);
    break;
  }
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Attention                                       */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  static __fp16 *F = l1_F; // Should be allocated dinamically
  static __fp16 *b = l1_b; // Should be allocated dinamically
  if (core_id == 0) {
    dma_memcpy_nonblocking(F, l2_F, Embed * Embed * Wf * sizeof(int16_t));
    dma_memcpy_nonblocking(b, l2_b, Embed * sizeof(int16_t));
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
  /* Permute result                                                         */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  permute_result(T2, T1, Beam, Embed, tdSamples, mode);
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Permute result                                  */\n");
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
  /* Compute convolution on output and sum                                  */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  conv1d(T1, F, b, I, Embed, Embed, Wf, Beam, tdSamples);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#ifdef VERBOSE
  if (core_id == 0) {
    printf("/*********************************************************/\n");
    printf("/* DONE: Compute convolution on output                   */\n");
    printf("/*********************************************************/\n\n");
  }
  mempool_barrier(num_cores);
#endif

  mempool_barrier(num_cores);
  return T2;
}
