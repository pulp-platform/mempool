// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"

#include "baremetal/mempool_matmul_f16.h"
#include "builtins_v2.h"

/**
  @brief         Computes 1D im2col transformation.
  @param[in]     Ci         dimension input channel
  @param[in]     Wi         dimension convolution width
  @param[in]     Wf         dimension filter width
  @param[in]     X          input matrix  size: Cin * Win
  @param[in]     X_im2col   output matrix  size: Cin * Win * Wf
  @return        none
*/

/* 32-bit word (two fp16) that may alias the fp16 buffers */
typedef uint32_t __attribute__((may_alias)) im2col_w32_t;

/* Wf = 3: the three im2col rows of input row x are x[t-1], x[t], x[t+1].
 * With two fp16 per word (low half first), each output word combines the
 * current input word with the high half of the previous one or the low half
 * of the next one. Ww = Wi / 2 words. */
static inline void im2col1d_w3_row(im2col_w32_t const *__restrict__ x,
                                   im2col_w32_t *__restrict__ out,
                                   uint32_t Ww) {
  im2col_w32_t *o0 = out, *o1 = out + Ww, *o2 = out + 2 * Ww;
  uint32_t prev = 0, cur = x[0];
  for (uint32_t w = 0; w < Ww; w++) {
    uint32_t next = (w + 1 < Ww) ? x[w + 1] : 0;
    o0[w] = (prev >> 16) | (cur << 16); // x[t-1]
    o1[w] = cur;                        // x[t]
    o2[w] = (cur >> 16) | (next << 16); // x[t+1]
    prev = cur;
    cur = next;
  }
}

void im2col1d_f16(__fp16 const *__restrict__ X, __fp16 *__restrict__ X_im2col,
                  uint32_t Ci, uint32_t Wi, uint32_t Wf, uint32_t core_id,
                  uint32_t num_cores) {

  // Wf = 3 on word-aligned rows: one input row per core, three output rows
  if (Wf == 3 && (Wi & 1) == 0 &&
      (((uint32_t)X | (uint32_t)X_im2col) & 3) == 0) {
    for (uint32_t i = core_id; i < Ci; i += num_cores) {
      im2col1d_w3_row((im2col_w32_t const *)&X[i * Wi],
                      (im2col_w32_t *)&X_im2col[i * 3 * Wi], Wi / 2);
    }
    return;
  }

  uint32_t pad = Wf / 2;
  uint32_t i, k; // row, filter

  for (uint32_t i_out = core_id; i_out < Ci * Wf; i_out += num_cores) {
    i = i_out / Wf;
    k = i_out % Wf;
    __fp16 *__restrict__ Out = &X_im2col[i_out * Wi];
    __fp16 const *__restrict__ In = &X[i * Wi];
    // Splitting the padding out of the loop, instead of branching on every
    // j_out, leaves a plain shifted copy for the interior -- no per-element
    // branch.
    uint32_t j_out = 0;
    uint32_t lead_zeros = (k < pad) ? (pad - k) : 0;
    lead_zeros = lead_zeros < Wi ? lead_zeros : Wi;
    for (; j_out < lead_zeros; j_out++) {
      Out[j_out] = (__fp16)0;
    }
    uint32_t trail_zeros = (k > pad) ? (k - pad) : 0;
    uint32_t copy_end = trail_zeros < Wi ? (Wi - trail_zeros) : j_out;
    for (; j_out < copy_end; j_out++) {
      Out[j_out] = In[j_out + k - pad];
    }
    for (; j_out < Wi; j_out++) {
      Out[j_out] = (__fp16)0;
    }
  }

  return;
}

/* Callback to im2col of an input stored as B * Ci * Wi */
static inline void im2col_dense(__fp16 const *__restrict__ X,
                                __fp16 *__restrict__ X_im2col, uint32_t b0,
                                uint32_t nb, uint32_t Ci, uint32_t Wi,
                                uint32_t Wf, uint32_t core_id,
                                uint32_t num_cores) {
  im2col1d_f16(&X[b0 * Ci * Wi], &X_im2col[b0 * Ci * Wi * Wf], nb * Ci, Wi, Wf,
               core_id, num_cores);
}

/**
  @brief         Computes 1D convolution.
  @param[in]     B      batch size
  @param[in]     Ci     dimension input channel
  @param[in]     Co     dimension output channel
  @param[in]     Wi     dimension convolution width
  @param[in]     Wf     dimension filter width
  @param[in]     X      input matrix  size: loop * Cin * Win
  @param[in]     F      filter matrix size: Cout * Cin * Wf
  @param[out]    Y      output matrix size: loop * Cout * Win
  @param[in]     im2col if 1 execute im2col implementation
  @return        none
*/

void conv1d_f16(__fp16 const *__restrict__ X, __fp16 const *__restrict__ F,
                __fp16 *__restrict__ Y,
                __attribute__((unused)) __fp16 *__restrict__ X_im2col,
                uint32_t B, uint32_t Ci, uint32_t Co, uint32_t Wi, uint32_t Wf,
                uint32_t im2col, uint32_t core_id, uint32_t num_cores) {

  if (im2col) {

    // Transformation
    im2col1d_f16(X, X_im2col, B * Ci, Wi, Wf, core_id, num_cores);
    mempool_barrier(num_cores);
    mempool_stop_benchmark();

    mempool_start_benchmark();
    if (NUM_REDMULE_TILES > 0) {

      uint32_t redmule_id = mempool_get_redmule_id();
      uint32_t num_redmules = mempool_get_redmule_count();
      for (uint32_t ii = redmule_id; ii < B; ii += num_redmules) {
        if (redmule_id < num_redmules) {
          unsigned int I_ptr = (unsigned int)(F);
          unsigned int W_ptr = (unsigned int)(&X_im2col[ii * Ci * Wi * Wf]);
          unsigned int O_ptr = (unsigned int)(&Y[ii * Co * Wi]);
          uint16_t M = (uint16_t)(Co);
          uint16_t N = (uint16_t)(Ci * Wf);
          uint16_t P = (uint16_t)(Wi);
          hwpe_soft_clear();
          mempool_wait(10);
          redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, MATMUL, Float16);
          mempool_wait(10);
          hwpe_trigger_job();
          mempool_wfi();
        }
      }

    } else {

      uint32_t num_cores_batch = Wi / 2;
      uint32_t core_id_batch = core_id % num_cores_batch;

      uint32_t group_id = core_id / num_cores_batch;
      uint32_t num_groups = num_cores / num_cores_batch;

      for (uint32_t ii = group_id; ii < B; ii += num_groups) {
        __fp16 *W_ptr = &X_im2col[ii * Ci * Wi * Wf];
        __fp16 *O_ptr = &Y[ii * Co * Wi];
        matmul_4x2_parallel_f16vec(F, W_ptr, O_ptr, Co, Ci * Wf, Wi,
                                   core_id_batch, num_cores_batch);
      }
    }

  } else {

    uint32_t pad = Wf / 2;
    for (uint32_t bb = core_id; bb < (B * Co); bb += num_cores) {

      uint32_t ii = bb / Co;
      uint32_t i_out = bb % Co;
      for (uint32_t j_out = 0; j_out < Wi; j_out++) {

        __fp16 sum = 0.0f;
        for (uint32_t k = 0; k < Wf; k++) {
          int32_t j = (int32_t)j_out - (int32_t)pad + (int32_t)k;
          if (j >= 0 && j < (int32_t)Wi) {

            for (uint32_t i = 0; i < Ci; i++) {
              uint32_t x_idx = ii * Ci * Wi + i * Wi + (uint32_t)j;
              uint32_t f_idx = (i_out * Ci + i) * Wf + k;
              asm volatile("fmadd.h %[s], %[x], %[f], %[s];"
                           : [s] "+&r"(sum)
                           : [x] "r"(X[x_idx]), [f] "r"(F[f_idx]));
            }
          }
        }
        Y[(ii * Co + i_out) * Wi + j_out] = sum;
      }
    }
  }

  mempool_barrier(num_cores);
  return;
}

/**
  @brief         Post-operation applied in place on a chunk of conv1d output.
  @param[in,out] data       output chunk
  @param[in]     size       number of elements in the chunk
  @param[in]     core_id    core ID
  @param[in]     num_cores  number of cores
*/

typedef void (*conv1d_post_t)(__fp16 *__restrict__ data, uint32_t size,
                              uint32_t core_id, uint32_t num_cores);

/**
  @brief         im2col of the batches [b0, b0 + nb) of a pipelined conv1d.
  @param[in]     X          input, as passed to the convolution
  @param[out]    X_im2col   im2col buffer of the whole convolution
*/

typedef void (*conv1d_im2col_t)(__fp16 const *__restrict__ X,
                                __fp16 *__restrict__ X_im2col, uint32_t b0,
                                uint32_t nb, uint32_t Ci, uint32_t Wi,
                                uint32_t Wf, uint32_t core_id,
                                uint32_t num_cores);

/* A stage of conv1d_pipelined_f16: one convolution */
typedef struct {
  conv1d_im2col_t im2col; // im2col of a chunk of the stage input
  __fp16 const *X;        // stage input, as read by im2col
  __fp16 *cols;           // im2col buffer, [B][Ci * Wf][Wi]
  __fp16 const *F;        // weights, Co * Ci * Wf
  __fp16 *Y;              // stage output, [B][Co][Wi]
  uint16_t Ci, Co;        // 16 bits: the stages are on the stack
} conv1d_stage_t;

/**
  @brief         Computes S 1D convolutions, each reading the output of the
                 previous one batch by batch, pipelining im2col and GEMM.
  @details       The B batches are processed in chunks of one batch per
                 RedMulE, the GEMM tasks are numbered stage by stage, chunk by
                 chunk. Round k: the RedMulEs compute GEMM task k - 1, while
                 all cores compute the im2col of task k and, when post is not
                 NULL, apply post in place on the output of task k - 2 if it
                 belongs to the last stage. The im2col of task k reads the
                 output of task k - chunks: the stages are one pipeline, which
                 fills and drains once. Two consecutive stages only touch
                 different chunks of a shared buffer within a round. With a
                 single chunk, the stages run one after the other. Without
                 RedMulEs, transforms the whole input of each stage and
                 computes its GEMMs with conv1d_f16().
                 Every core reads the stages: they must not be in a shared L1
                 buffer, where all the cores would load the same words at once
                 (they are on the stack of the caller, e.g. a compound literal
                 for one stage).
  @param[in]     st         the S stages
  @param[in]     S          number of stages
  @param[in]     post       in-place post-operation on the output of the last
                            stage, or NULL
  @param[in]     B          batch size
  @param[in]     Wi         dimension convolution width
  @param[in]     Wf         dimension filter width
  @param[in]     core_id    core ID
  @param[in]     num_cores  number of cores
  @return        none
*/
static inline void conv1d_pipelined_f16(conv1d_stage_t const *st, uint32_t S,
                                        conv1d_post_t post, uint32_t B,
                                        uint32_t Wi, uint32_t Wf,
                                        uint32_t core_id, uint32_t num_cores) {

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t chunk = mempool_get_redmule_count();

  if (chunk == 0) {
    // The GEMMs read the im2col buffer (an im2col with Wf = 1 is the identity)
    for (uint32_t i = 0; i < S; i++) {
      conv1d_stage_t const *s = &st[i];
      s->im2col(s->X, s->cols, 0, B, s->Ci, Wi, Wf, core_id, num_cores);
      mempool_barrier(num_cores);
      conv1d_f16(s->cols, s->F, s->Y, s->cols, B, s->Ci * Wf, s->Co, Wi, 1, 1,
                 core_id, num_cores);
      mempool_barrier(num_cores);
    }
    if (post) {
      post(st[S - 1].Y, B * st[S - 1].Co * Wi, core_id, num_cores);
      mempool_barrier(num_cores);
    }
    return;
  }

  uint32_t chunks = (B + chunk - 1) / chunk;
  // With a single chunk, the im2col of a stage would read the output of the
  // GEMMs that run in the same round: pipeline the stages one at a time. This
  // is a loop and not a recursive call, whose extra frame overflows the stack
  uint32_t per = (chunks == 1) ? 1 : S;
  for (uint32_t g = 0; g < S; g += per) {
    conv1d_stage_t const *sg = &st[g];
    conv1d_post_t pg = (g + per == S) ? post : NULL;
    uint32_t tasks = per * chunks;
    uint32_t rounds = tasks + (pg ? 2 : 1);

    for (uint32_t k = 0; k < rounds; k++) {

      // GEMM of task k - 1
      uint32_t launched = 0;
      if (k >= 1 && k - 1 < tasks) {
        conv1d_stage_t const *s = &sg[(k - 1) / chunks];
        uint32_t ii = ((k - 1) % chunks) * chunk + redmule_id;
        launched = (redmule_id < chunk) && (ii < B);
        if (launched) {
          hwpe_soft_clear();
          mempool_wait(10);
          redmule_cfg((unsigned int)s->F,
                      (unsigned int)&s->cols[ii * s->Ci * Wf * Wi],
                      (unsigned int)&s->Y[ii * s->Co * Wi], (uint16_t)s->Co,
                      (uint16_t)(s->Ci * Wf), (uint16_t)Wi, 0, MATMUL, Float16);
          mempool_wait(10);
          hwpe_trigger_job();
        }
      }

      // im2col of task k
      if (k < tasks) {
        conv1d_stage_t const *s = &sg[k / chunks];
        uint32_t b0 = (k % chunks) * chunk;
        uint32_t nb = (B - b0 < chunk) ? (B - b0) : chunk;
        s->im2col(s->X, s->cols, b0, nb, s->Ci, Wi, Wf, core_id, num_cores);
      }

      // Post-operation of task k - 2 (GEMM completed in the previous round)
      if (pg && k >= 2 && k - 2 < tasks && (k - 2) / chunks == per - 1) {
        conv1d_stage_t const *s = &sg[per - 1];
        uint32_t b0 = ((k - 2) % chunks) * chunk;
        uint32_t nb = (B - b0 < chunk) ? (B - b0) : chunk;
        pg(&s->Y[b0 * s->Co * Wi], nb * s->Co * Wi, core_id, num_cores);
      }

      // Wait for RedMulE (the wake-up is latched if the job already finished)
      if (launched) {
        mempool_wfi();
      }
      mempool_barrier(num_cores);
    }
  }
}
