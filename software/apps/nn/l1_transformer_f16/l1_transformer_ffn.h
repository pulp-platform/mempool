// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_conv1d_f16.h"
#include "baremetal/mempool_gelu_f16.h"
#include "baremetal/mempool_layernorm_f16.h"

/**
  @brief         Computes the feed-forward block.
  @param[in]     l2_I      Input tensor in L2 memory, used when in is NULL
  @param[in]     l2_F      Convolution filter weights in L2 memory
  @param[in]     in        Output of the previous layer in L1, or NULL
  @return        Output of the layer in L1, [Beam][Embed][tdSamples]
*/

__fp16 *ffn(__fp16 const *__restrict__ l2_I, __fp16 const *__restrict__ l2_F,
            __fp16 const *in, uint32_t Beam, uint32_t Embed, uint32_t tdSamples,
            uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Data of this layer and the L1 buffer that holds it (see l2_data.h). A
  // buffer is reused once nothing reads its previous content any more.

  //   x       input [Beam][Embed][tdSamples]     l1.x
  //   cols    im2col of the convolutions         l1.im2col1
  //   up      up-projection [Beam][2*Embed][..]  l1.proj
  //   hidden  Gelu of up                         in place
  //   y       output [Beam][Embed][tdSamples]    l1.x

  __fp16 *x = l1.x;
  __fp16 *cols = l1.im2col1;
  __fp16 *up = l1.proj;
  __fp16 *hidden = up;
  __fp16 *y = l1.x;
  __fp16 *F = l1.F;
#ifndef PIPELINED
  __fp16 *x_norm = l1.im2col2;
#endif

  /**************************************************************************/
  /* Transfer inputs                                                        */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    // The input is the output of the previous layer when there is one.
    if (in == NULL) {
      dma_memcpy_blocking(x, l2_I, Beam * Embed * tdSamples * sizeof(int16_t));
    }
    dma_memcpy_blocking(F, l2_F, Embed * Embed * 2 * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer inputs");

  /**************************************************************************/
  /* Layernorm                                                              */
  /**************************************************************************/

  // Layer Normalization (over the raw Embed-channel input). With PIPELINED it
  // runs in the convolution, as its im2col (layernorm_im2col): the region
  // stays (empty) so that the region indices do not change
  mempool_start_benchmark();
#ifndef PIPELINED
  uint32_t num_cores_per_batch = num_cores / Beam;
  uint32_t batch_id = core_id % num_cores_per_batch;
  uint32_t idx = core_id / num_cores_per_batch;
  layernorm_parallel_2x4_f16vec(&x[idx * Embed * tdSamples],
                                &x_norm[idx * Embed * tdSamples], Embed,
                                tdSamples, batch_id, num_cores_per_batch);
#endif
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Layernorm");

#ifdef PIPELINED
  /**************************************************************************/
  /* Conv1D + Gelu                                                          */
  /**************************************************************************/

  // Convolution: up-projection (Embed -> 2*Embed), Gelu applied in place
  mempool_start_benchmark();
  conv1d_pipelined_f16(&(conv1d_stage_t){layernorm_im2col, x, cols, F, up,
                                         (uint16_t)Embed,
                                         (uint16_t)(2 * Embed)},
                       1, gelu_f16, Beam, tdSamples, Wf, core_id, num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution + Gelu");
#else
  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: up-projection (Embed -> 2*Embed)
  mempool_start_benchmark();
  conv1d_f16(x_norm, F, up, cols, Beam, Embed, Embed * 2, tdSamples, Wf, 1,
             core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution");

  /**************************************************************************/
  /* Gelu                                                                   */
  /**************************************************************************/

  // Gelu in place on up
  mempool_start_benchmark();
  gelu_f16(hidden, Beam * Embed * 2 * tdSamples, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Gelu");
#endif

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, Embed * Embed * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer weights");

  /**************************************************************************/
  /* Conv1D                                                                 */
  /**************************************************************************/

  // Convolution: down-projection (2*Embed -> Embed)
  mempool_start_benchmark();
#ifdef PIPELINED
  conv1d_pipelined_f16(&(conv1d_stage_t){im2col_dense, hidden, cols, F, y,
                                         (uint16_t)(2 * Embed),
                                         (uint16_t)Embed},
                       1, NULL, Beam, tdSamples, Wf, core_id, num_cores);
#else
  conv1d_f16(hidden, F, y, cols, Beam, Embed * 2, Embed, tdSamples, Wf, 1,
             core_id, num_cores);
#endif
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Compute convolution on output");

  return y;
}

#ifdef FUSE_CHAIN
// FUSE_CHAIN: the convolutions between two attentions work on each beam on
// its own (output projection, FFN up-projection + gelu, FFN down-projection,
// QKV projection of the next layer + permutation), so they run as one
// pipeline instead of one pipeline per convolution. The GEMMs of a stage are
// split in chunks of one beam per RedMulE: round k, the RedMulEs compute GEMM
// task k - 1 (stage-major: all chunks of a stage, then the next stage) while
// the cores compute the im2col of task k, which reads the output of task
// k - chunks. The pipeline fills and drains once per chain instead of once
// per convolution.

// gelu of the up-projection output, then its im2col for the down-projection:
// each core applies the gelu to the rows it transforms
static void gelu_im2col(__fp16 const *__restrict__ X,
                        __fp16 *__restrict__ X_im2col, uint32_t b0, uint32_t nb,
                        uint32_t Ci, uint32_t Wi, uint32_t Wf, uint32_t core_id,
                        uint32_t num_cores) {
  __fp16 *h = (__fp16 *)X;
  for (uint32_t r = b0 * Ci + core_id; r < (b0 + nb) * Ci; r += num_cores) {
    gelu_f16(&h[r * Wi], Wi, 0, 1);
    im2col1d_f16(&h[r * Wi], &X_im2col[r * Wf * Wi], 1, Wi, Wf, 0, 1);
  }
}

/**
  @brief         Output projection and FFN of a layer, then, with next_qkv,
                 the QKV projection and permutation of the next layer.
  @param[in]     att       attention output (in l1.im2col1)
  @param[in]     mode      layout of att
  @param[in]     next_qkv  1: also the QKV projection of the next layer
  @param[in]     next_mode attention mode of the next layer
  @return        output of the FFN, [Beam][Embed][tdSamples]
*/
__fp16 *ffn_chain(__fp16 const *__restrict__ l2_F, __fp16 const *att,
                  permute_mode_t mode, uint32_t next_qkv,
                  permute_mode_t next_mode, uint32_t Beam, uint32_t Embed,
                  uint32_t tdSamples, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Buffers. Two consecutive stages only touch different chunks of a shared
  // buffer: the im2col of stage s + 1 on chunk c runs while the RedMulEs read
  // the im2col of stage s on chunk c + 1
  //   out-proj  im2col l1.im2col2  output l1.x
  //   up        im2col l1.im2col2  output l1.proj (hidden)
  //   down      im2col l1.im2col1  output l1.x
  //   qkv       im2col l1.im2col1  output l1.proj, then q, kt, v in l1.qkv

  __fp16 *y_out = l1.x;
  __fp16 *hidden = l1.proj;
  __fp16 *y = l1.x;
  __fp16 *qkv = l1.proj;

  // Transfer weights
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(&l1.F[FC_OUT], l2_F, FC_OUT_SIZE * sizeof(int16_t));
    dma_memcpy_blocking(&l1.F[FC_UP], l2_F, FC_UP_SIZE * sizeof(int16_t));
    dma_memcpy_blocking(&l1.F[FC_DOWN], l2_F, FC_DOWN_SIZE * sizeof(int16_t));
    if (next_qkv) {
      dma_memcpy_blocking(l1.F, l2_F, FC_QKV_SIZE * sizeof(int16_t));
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer weights");

  // On the stack of every core: in L1, all the cores would read the same
  // words. One array: conv1d_pipelined_f16 reads consecutive stages.
  conv1d_stage_t st[4] = {
      // Output projection
      {(mode == TBE) ? im2col_att_tbe : im2col_att_ebt, att, l1.im2col2,
       &l1.F[FC_OUT], y_out, (uint16_t)Embed, (uint16_t)Embed},
      // FFN up-projection
      {layernorm_im2col, y_out, l1.im2col2, &l1.F[FC_UP], hidden,
       (uint16_t)Embed, (uint16_t)(2 * Embed)},
      // FFN down-projection, the gelu applied in its im2col
      {gelu_im2col, hidden, l1.im2col1, &l1.F[FC_DOWN], y,
       (uint16_t)(2 * Embed), (uint16_t)Embed},
      // QKV projection of the next layer (with next_qkv)
      {layernorm_im2col, y, l1.im2col1, l1.F, qkv, (uint16_t)Embed,
       (uint16_t)(3 * Embed)},
  };

  mempool_start_benchmark();
  if (next_qkv) {
    conv1d_pipelined_f16(
        st, 4, (next_mode == TBE) ? permute_post_tbe : permute_post_ebt, Beam,
        tdSamples, Wf, core_id, num_cores);
  } else {
    conv1d_pipelined_f16(st, 3, NULL, Beam, tdSamples, Wf, core_id, num_cores);
  }
  mempool_stop_benchmark();
  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution chain");

  return y;
}
#endif
