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

void permute_result(__fp16 const *__restrict__ IN,
                    __fp16 *__restrict__ OUT,
                    uint32_t Beam, uint32_t Embed,
                    uint32_t tdSamples, permute_mode_t mode);

void permute_qkv(__fp16 const *__restrict__ IN,
                 __fp16 *__restrict__ Q,
                 __fp16 *__restrict__ Kt,
                 __fp16 *__restrict__ V,
                 uint32_t Beam, uint32_t Embed,
                 uint32_t tdSamples, permute_mode_t mode);

void attention_block(__fp16 const *__restrict__ Q,
                     __fp16 const *__restrict__ Kt,
                     __fp16 const *__restrict__ V,
                     __fp16 *__restrict__ Aw,
                     __fp16 *__restrict__ A,
                     uint32_t Batch, uint32_t SeqLen,
                     uint32_t tdEmbed);

/**
  @brief         Computes the full attention block.
  @details       Executes the following pipeline:
                   1. DMA transfer of inputs and weights
                   2. Layer normalization
                   3. 1D convolution for QKV projection
                   4. Attention computation
                 The function exploits mempool cores, DMA engines,
                 and RedMule accelerators when available.

  @param[in]     l2_I      Input tensor in L2 memory, used when in is NULL
  @param[in]     in        Output of the previous layer in L1, or NULL
  @param[in]     l2_F      Convolution filter weights in L2 memory
  @param[in]     l2_b      Convolution bias vector in L2 memory
  @param[in]     Beam      Beam size
  @param[in]     Embed     Embedding dimension
  @param[in]     tdSamples Number of temporal samples
  @param[in]     Wf        Dimension convolution
  @param[in]     mode      Attention is executed in the temporal/embed domain.
  @return        Output of the layer in L1, [Beam][Embed][tdSamples]
*/

__fp16 *attention(__fp16 const *__restrict__ l2_I,
                  __fp16 const *__restrict__ l2_F,
                  __fp16 const *in,
                  uint32_t Beam, uint32_t Embed, uint32_t tdSamples,
                  uint32_t Wf, permute_mode_t mode) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Data of this layer and the L1 buffer that holds it (see l2_data.h). A
  // buffer is reused once nothing reads its previous content any more.

  //   x       input [Beam][Embed][tdSamples]     l1_arena.x
  //   x_norm  layernorm output                   l1_act
  //   qkv     QKV projection [Beam][3*Embed][..] l1_arena.y      over x
  //   cols    im2col of the convolutions         l1_scratch
  //   q,kt,v  attention operands                 l1_act          over x_norm
  //   Aw      softmax output                     l1_arena.y      over qkv
  //   att     scores, then attention output      l1_scratch      over cols
  //   att_p   att as [Beam][Embed][tdSamples]    l1_act          over q,kt,v
  //   y       output [Beam][Embed][tdSamples]    l1_arena.y      over Aw

  __fp16 *x = l1_arena.x;
  __fp16 *x_norm = l1_act;
  __fp16 *qkv = l1_arena.y;
  __fp16 *cols = l1_scratch;
  __fp16 *Aw = l1_arena.x;
  __fp16 *att = &l1_scratch[TS_A_OFFSET];
  __fp16 *att_p = l1_act;
  __fp16 *y = l1_arena.y;
  __fp16 *F = l1_F;

  // Batches of the attention: Embed (EBT) or tdSamples (TBE), with sequences
  // of Beam elements and embeddings of tdEmbed. Their slots in q, kt and v
  // are padded by TS_SLOT (see l2_data.h).

  uint32_t nb = (mode == TBE) ? tdSamples : Embed;
  uint32_t td = (mode == TBE) ? Embed : tdSamples;
  uint32_t slot = TS_SLOT(Beam * td);

  __fp16 *q = l1_act;
  __fp16 *kt = &l1_act[TS_KT_OFFSET(nb, slot)];
  __fp16 *v = &l1_act[TS_V_OFFSET(nb, slot)];

  /**************************************************************************/
  /* Transfer inputs                                                        */
  /**************************************************************************/

  // The input is the output of the previous layer when there is one: it is
  // already in L1, and moved to x only if it is somewhere else.

  mempool_start_benchmark();
  if (core_id == 0) {
    if (in == NULL) {
      dma_memcpy_blocking(x, l2_I, Beam * Embed * tdSamples * sizeof(int16_t));
    } else if (in != x) {
      dma_memcpy_blocking(x, in, Beam * Embed * tdSamples * sizeof(int16_t));
    }
    dma_memcpy_blocking(F, l2_F, F_BYTES(Embed * Embed * 3 * Wf));
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

  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(&x[idx * Embed * tdSamples],
                                &x_norm[idx * Embed * tdSamples], Embed,
                                tdSamples, batch_id, num_cores_per_batch);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Layernorm");

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: QKV projection (Embed -> 3*Embed)
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(x_norm, F, F_STRIDE, qkv, cols, Beam, Embed, Embed * 3,
                       tdSamples, Wf, NULL, core_id, num_cores);
#else
  conv1d_f16(x_norm, F, qkv, cols, Beam, Embed, Embed * 3, tdSamples, Wf, 1,
             core_id, num_cores);
#endif
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution");

  /**************************************************************************/
  /* Permute to QKV                                                         */
  /**************************************************************************/

  mempool_start_benchmark();
  permute_qkv(qkv, q, kt, v, Beam, Embed, tdSamples, mode);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Permute to QKV");

  /**************************************************************************/
  /* Attention                                                              */
  /**************************************************************************/

  attention_block(q, kt, v, Aw, att, nb, Beam, td);

  PRINT_DONE(VERBOSE, core_id, num_cores, "Attention");

  /**************************************************************************/
  /* Permute result                                                         */
  /**************************************************************************/

  mempool_start_benchmark();
  permute_result(att, att_p, Beam, Embed, tdSamples, mode);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Permute result");

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  // Transfer weights: output projection (Embed -> Embed)
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, F_BYTES(Embed * Embed * Wf));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: output projection (Embed -> Embed)
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(att_p, F, F_STRIDE, y, cols, Beam, Embed, Embed,
                       tdSamples, Wf, NULL, core_id, num_cores);
#else
  conv1d_f16(att_p, F, y, cols, Beam, Embed, Embed, tdSamples, Wf, 1, core_id,
             num_cores);
#endif
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution");

  return y;
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
  @param[out]    Aw        Softmax output, [Batch][SeqLen][SeqLen]
  @param[out]    A         Attention scores Q * Kt, [Batch][SeqLen][SeqLen],
                           then attention output, [Batch][SeqLen][tdEmbed]
  @param[in]     Batch     Number of batches
  @param[in]     SeqLen    Sequence Length
  @param[in]     tdEmbed   Temporal embedding dimension
  @return        none
*/

void attention_block(__fp16 const *__restrict__ Q,
                     __fp16 const *__restrict__ Kt,
                     __fp16 const *__restrict__ V,
                     __fp16 *__restrict__ Aw,
                     __fp16 *__restrict__ A, uint32_t Batch, uint32_t SeqLen,
                     uint32_t tdEmbed) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // The scores and the attention output share A
  __fp16 *scores = A;

  // Batch slots of Q, Kt, V
  uint32_t slot_q = TS_SLOT(SeqLen * tdEmbed);
  uint32_t slot_s = TS_SLOT(SeqLen * SeqLen);

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

#ifdef PIPELINED
  // Pipelined Q*Kt and Softmax
  // Round r: RedMulEs compute Q*Kt for batches [r*R, (r+1)*R), while all
  // cores compute the softmax of the batches produced in round r-1.
  // One extra round drains the softmax of the last batches.
  mempool_start_benchmark();
  for (uint32_t bb = 0; bb < Batch + num_redmules; bb += num_redmules) {

    // Launch Q*Kt of the current batches
    uint32_t ii = bb + redmule_id;
    uint32_t launched = (redmule_id < num_redmules) && (ii < Batch);
    if (launched) {
      unsigned int I_ptr = (unsigned int)(Q + ii * slot_q);
      unsigned int W_ptr = (unsigned int)(Kt + ii * slot_q);
      unsigned int O_ptr = (unsigned int)(scores + ii * slot_s);
      uint16_t M = (uint16_t)SeqLen;
      uint16_t N = (uint16_t)tdEmbed;
      uint16_t P = (uint16_t)SeqLen;
#ifdef REDMULE_ZERO_OUTPUT
      // Verification only: RedMulE accumulates into its output
      for (uint32_t z = 0; z < (uint32_t)M * P; z++) {
        ((uint16_t *)O_ptr)[z] = 0;
      }
#endif
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, GEMM, Float16);
      mempool_wait(10);
      hwpe_trigger_job();
    }

    // Softmax of the batches computed in the previous round
    if (bb > 0) {
      uint32_t prev = bb - num_redmules;
      uint32_t nb = (Batch - prev < num_redmules) ?
                    (Batch - prev) : num_redmules;
      uint32_t num_cores_per_softmax = num_cores / nb;
      uint32_t softmax_id = core_id % num_cores_per_softmax;
      uint32_t idx = core_id / num_cores_per_softmax;
      if (idx < nb) {
        uint32_t jj = prev + idx;
        softmax_parallel_2x4_f16vec(&scores[jj * slot_s],
                                    &Aw[jj * slot_s], SeqLen, SeqLen,
                                    softmax_id, num_cores_per_softmax);
      }
    }

    // Wait for RedMulE (the wake-up is latched if the job already finished)
    if (launched) {
      mempool_wfi();
    }
    mempool_barrier(num_cores);

  }
  mempool_stop_benchmark();
#else
  // Q*Kt
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(Q + i * slot_q);
      unsigned int W_ptr = (unsigned int)(Kt + i * slot_q);
      unsigned int O_ptr = (unsigned int)(scores + i * slot_s);
      uint16_t M = (uint16_t)SeqLen;
      uint16_t N = (uint16_t)tdEmbed;
      uint16_t P = (uint16_t)SeqLen;

#ifdef REDMULE_ZERO_OUTPUT
      // Verification only: RedMulE accumulates into its output
      for (uint32_t z = 0; z < (uint32_t)M * P; z++) {
        ((uint16_t *)O_ptr)[z] = 0;
      }
#endif

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
    softmax_parallel_2x4_f16vec(&scores[idx * slot_s],
                                &Aw[idx * slot_s], SeqLen, SeqLen,
                                softmax_id, num_cores_per_softmax);
  } else {
    for (uint32_t i = core_id; i < Batch; i += num_cores) {
      softmax_parallel_2x4_f16vec(&scores[i * slot_s],
                                  &Aw[i * slot_s], SeqLen, SeqLen, 0,
                                  1);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  // A = Softmax(Q*Kt)*V
  mempool_start_benchmark();
  if (redmule_id < num_redmules) {
    for (uint32_t i = redmule_id; i < Batch; i += num_redmules) {
      unsigned int I_ptr = (unsigned int)(Aw + i * slot_s);
      unsigned int W_ptr = (unsigned int)(V + i * slot_q);
      unsigned int O_ptr = (unsigned int)(A + i * slot_q);
      uint16_t M = (uint16_t)SeqLen;
      uint16_t N = (uint16_t)SeqLen;
      uint16_t P = (uint16_t)tdEmbed;
#ifdef REDMULE_ZERO_OUTPUT
      // Verification only: RedMulE accumulates into its output
      for (uint32_t z = 0; z < (uint32_t)M * P; z++) {
        ((uint16_t *)O_ptr)[z] = 0;
      }
#endif
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

  // Batch slot of Q, Kt and V (see TS_SLOT in l2_data.h)
  uint32_t slot = TS_SLOT(Beam * ((mode == TBE) ? Embed : tdSamples));

  for (uint32_t i = core_id; i < Beam * Embed; i += num_cores) {
    uint32_t b = i / Embed;
    uint32_t e = i % Embed;
    switch (mode) {
      case TBE:
        for (uint32_t t = 0; t < tdSamples; t++) {
          uint32_t o_idx, o_tidx, i_idx;
          i_idx = (b * Embed + e) * 3 * tdSamples + t;
          o_idx = t * slot + b * Embed + e;
          o_tidx = t * slot + e * Beam + b;
          Q[o_idx] = IN[i_idx];
          Kt[o_tidx] = IN[i_idx + Embed * tdSamples];
          V[o_idx] = IN[i_idx + 2 * Embed * tdSamples];
        }
        break;
      default: { // EBT
        uint32_t i_base = (b * Embed + e) * 3 * tdSamples;
        uint32_t o_base = e * slot + b * tdSamples;
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
          uint32_t o_tidx = e * slot + t * Beam + b;
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

  // Batch slot of the attention output (see TS_SLOT in l2_data.h)
  uint32_t slot = TS_SLOT(Beam * ((mode == TBE) ? Embed : tdSamples));

  for (uint32_t i = core_id; i < Beam * Embed; i += num_cores) {
    uint32_t b = i / Embed;
    uint32_t e = i % Embed;
    switch (mode) {
    case TBE:
      for (uint32_t t = 0; t < tdSamples; t++) {
        uint32_t i_idx, o_idx;
        i_idx = t * slot + b * Embed + e;
        o_idx = (b * Embed + e) * tdSamples + t;
        OUT[o_idx] = IN[i_idx];
      }
      break;
    default: { // EBT
      // IN and OUT are both contiguous in t here, so this is a
      // straight shifted copy: move it with v2h two elements at a time.
      uint32_t i_base = e * slot + b * tdSamples;
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
