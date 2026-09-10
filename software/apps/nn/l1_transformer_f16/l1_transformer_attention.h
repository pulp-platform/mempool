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
#include "baremetal/mempool_softmax_f16.h"

void permute_result(__fp16 const *__restrict__ IN, __fp16 *__restrict__ OUT,
                    uint32_t Beam, uint32_t Embed, uint32_t tdSamples,
                    permute_mode_t mode);
void permute_qkv(__fp16 const *__restrict__ IN, __fp16 *__restrict__ Q,
                 __fp16 *__restrict__ Kt, __fp16 *__restrict__ V, uint32_t Beam,
                 uint32_t Embed, uint32_t tdSamples, permute_mode_t mode);
void attention_block(__fp16 const *__restrict__ Q,
                     __fp16 const *__restrict__ Kt,
                     __fp16 const *__restrict__ V, __fp16 *__restrict__ A,
                     uint32_t Batch, uint32_t SeqLen, uint32_t tdEmbed);

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
  @return        none
*/

void attention(__fp16 const *__restrict__ l2_I, __fp16 const *__restrict__ l2_F,
               uint32_t Beam, uint32_t Embed, uint32_t tdSamples, uint32_t Wf,
               permute_mode_t mode) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  static __fp16 *I = l1_I;
  static __fp16 *F = l1_F;
  static __fp16 *T1 = l1_T1;
  static __fp16 *T2 = l1_T2;
  static __fp16 *T3 = l1_T3;

  __fp16 *X;
  __fp16 *Y;
  __fp16 *X_im2col;
  __fp16 *Q;
  __fp16 *Kt;
  __fp16 *V;

  /**************************************************************************/
  /* Transfer inputs                                                        */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    for (uint32_t b = 0; b < Beam; b++) {
      dma_memcpy_blocking(&I[b * Embed * tdSamples],
                          &l2_I[b * Embed * tdSamples],
                          Embed * tdSamples * sizeof(int16_t));
    }
    dma_memcpy_blocking(F, l2_F, Embed * Embed * 3 * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer inputs");

  /**************************************************************************/
  /* Layernorm                                                              */
  /**************************************************************************/

  // Layer Normalization (over the raw Embed-channel input)
  uint32_t num_cores_per_batch = num_cores / Beam;
  uint32_t batch_id = core_id % num_cores_per_batch;
  uint32_t idx = core_id / num_cores_per_batch;
  X = &I[idx * Embed * tdSamples];
  Y = &T1[idx * Embed * tdSamples];

  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(X, Y, Embed, tdSamples, batch_id,
                                num_cores_per_batch);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Layernorm");

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: QKV projection (Embed -> 3*Embed)
  X = T1;
  Y = T2;
  X_im2col = T3;

  mempool_start_benchmark();
  conv1d_f16(X, F, Y, X_im2col, Beam, Embed, Embed * 3, tdSamples, Wf, 1,
             core_id, num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution");

  /**************************************************************************/
  /* Permute to QKV                                                         */
  /**************************************************************************/

  Q = &T1[0 * Beam * Embed * tdSamples];
  Kt = &T1[1 * Beam * Embed * tdSamples];
  V = &T1[2 * Beam * Embed * tdSamples];

  mempool_start_benchmark();
  permute_qkv(T2, Q, Kt, V, Beam, Embed, tdSamples, mode);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Permute to QKV");

  /**************************************************************************/
  /* Attention                                                              */
  /**************************************************************************/

  switch (mode) {
  case TBE:
    attention_block(Q, Kt, V, T3, tdSamples, Beam, Embed);
    break;
  default: // EBT
    attention_block(Q, Kt, V, T3, Embed, Beam, tdSamples);
    break;
  }
  PRINT_DONE(VERBOSE, core_id, num_cores, "Attention");

  /**************************************************************************/
  /* Permute result                                                         */
  /**************************************************************************/

  mempool_start_benchmark();
  permute_result(T3, T1, Beam, Embed, tdSamples, mode);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Permute result");

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  // Transfer weights: output projection (Embed -> Embed)
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, Embed * Embed * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  X = T1;
  Y = T2;
  X_im2col = T3;

  mempool_start_benchmark();
  conv1d_f16(X, F, Y, X_im2col, Beam, Embed, Embed, tdSamples, Wf, 1, core_id,
             num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution");

  return;
}

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

  __fp16 *As = A;
  __fp16 *Aw = l1_Aw;

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  // Q*Kt
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(Q + i * (SeqLen * tdEmbed));
      unsigned int W_ptr = (unsigned int)(Kt + i * (tdEmbed * SeqLen));
      unsigned int O_ptr = (unsigned int)(As + i * (SeqLen * SeqLen));
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
  mempool_stop_benchmark();

  // Softmax
  mempool_start_benchmark();
  if (Batch < num_cores) {
    uint32_t num_cores_per_softmax = num_cores / Batch;
    uint32_t softmax_id = core_id % num_cores_per_softmax;
    uint32_t idx = core_id / num_cores_per_softmax;
    softmax_parallel_2x4_f16vec(&As[idx * (SeqLen * SeqLen)],
                                &Aw[idx * (SeqLen * SeqLen)], SeqLen, SeqLen,
                                softmax_id, num_cores_per_softmax);
  } else {
    for (uint32_t i = core_id; i < Batch; i += num_cores) {
      softmax_parallel_2x4_f16vec(&As[i * (SeqLen * SeqLen)],
                                  &Aw[i * (SeqLen * SeqLen)], SeqLen, SeqLen, 0,
                                  1);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // A = Softmax(Q*Kt)*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
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
  mempool_stop_benchmark();

  return;
}

/**
  @brief         Permutes and splits Q, K, V tensors from a packed input.
  @details       Converts input layout
                 [Beam][3*Embed][tdSamples]
                 into (depending on input mode):
                    - EBT:
                      Q  : [Embed][Beam][tdSamples]
                      V  : [Embed][Beam][tdSamples]
                      Kt : [Embed][tdSamples][Beam] (transposed for GEMM)
                    - TBE:
                      Q  : [tdSamples][Beam][Embed]
                      V  : [tdSamples][Beam][Embed]
                      Kt : [tdSamples][Embed][Beam] (transposed for GEMM)
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

  for (uint32_t i = core_id; i < Beam * Embed; i += num_cores) {
    uint32_t b = i / Embed;
    uint32_t e = i % Embed;
    switch (mode) {
    case TBE:
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t o_idx, o_tidx, i_idx;
        i_idx = (b * Embed + e) * 3 * tdSamples + t;
        o_idx = (t * Beam + b) * Embed + e;
        o_tidx = (t * Embed + e) * Beam + b;
        Q[o_idx] = IN[i_idx];
        Kt[o_tidx] = IN[i_idx + Embed * tdSamples];
        V[o_idx] = IN[i_idx + 2 * Embed * tdSamples];
      }
      break;
    default: { // EBT
      uint32_t i_base = (b * Embed + e) * 3 * tdSamples;
      uint32_t o_base = (e * Beam + b) * tdSamples;
      // Q and V are contiguous in t on both the IN side and their own side
      // (stride 1), so two t's at a time move through one v2h load/store
      uint32_t t = 0;
      if ((tdSamples & 1u) == 0) {
        for (; t < tdSamples; t += 2) {
          *(v2h *)&Q[o_base + t] = *(v2h *)&IN[i_base + t];
          *(v2h *)&V[o_base + t] =
              *(v2h *)&IN[i_base + t + 2 * Embed * tdSamples];
        }
      } else {
        for (; t < tdSamples; t++) {
          Q[o_base + t] = IN[i_base + t];
          V[o_base + t] = IN[i_base + t + 2 * Embed * tdSamples];
        }
      }
      for (t = 0; t < tdSamples; t++) {
        uint32_t o_tidx = (e * tdSamples + t) * Beam + b;
        Kt[o_tidx] = IN[i_base + t + Embed * tdSamples];
      }
      break;
    }
    }
  }

  return;
}

/**
  @brief         Depending on input mode:
                 - EBT: [Embed][Beam][tdSamples] -> [Beam][Embed][tdSamples].
                 - TBE: [tdSamples][Beam][Embed] -> [Beam][Embed][tdSamples].
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
    default: { // EBT
      // IN and OUT are both contiguous in t here, so this is a
      // straight shifted copy: move it with v2h two elements at a time.
      uint32_t i_base = (e * Beam + b) * tdSamples;
      uint32_t o_base = (b * Embed + e) * tdSamples;
      if ((tdSamples & 1u) == 0) {
        for (uint32_t t = 0; t < tdSamples; t += 2) {
          *(v2h *)&OUT[o_base + t] = *(v2h *)&IN[i_base + t];
        }
      } else {
        for (uint32_t t = 0; t < tdSamples; t++) {
          OUT[o_base + t] = IN[i_base + t];
        }
      }
      break;
    }
    }
  }

  return;
}
