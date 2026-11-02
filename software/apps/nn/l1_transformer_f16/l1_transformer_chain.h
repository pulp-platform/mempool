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
  @param[in]     att       attention output (in l1_scratch)
  @param[in]     mode      layout of att
  @param[in]     next_qkv  1: also the QKV projection of the next layer
  @param[in]     next_mode attention mode of the next layer
  @return        output of the FFN, [Beam][Embed][tdSamples]
*/
__fp16 *chain(__fp16 const *__restrict__ l2_F, __fp16 const *att,
              permute_mode_t mode, uint32_t next_qkv, permute_mode_t next_mode,
              uint32_t Beam, uint32_t Embed, uint32_t tdSamples, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Buffers. Two consecutive stages only touch different chunks of a shared
  // buffer: the im2col of stage s + 1 on chunk c runs while the RedMulEs read
  // the im2col of stage s on chunk c + 1
  //   out-proj  im2col l1_act      output l1_arena.aw[0, BET)
  //   up        im2col l1_act      output l1_arena.aw[BET, 3 BET)
  //   down      im2col l1_scratch  output l1_arena.aw[0, BET)
  //   qkv       im2col l1_scratch  output l1_arena.aw[BET, 4 BET),
  //                                       then q, kt, v in l1_act

  __fp16 *y_out = l1_arena.aw;
  __fp16 *hidden = &l1_arena.aw[X_SIZE];
  __fp16 *y = l1_arena.aw;
  __fp16 *qkv = &l1_arena.xy[X_SIZE];

  // Transfer weights
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(&l1_F[FC_OUT], l2_F, FC_OUT_SIZE * sizeof(int16_t));
    dma_memcpy_blocking(&l1_F[FC_UP], l2_F, FC_UP_SIZE * sizeof(int16_t));
    dma_memcpy_blocking(&l1_F[FC_DOWN], l2_F, FC_DOWN_SIZE * sizeof(int16_t));
    if (next_qkv) {
      dma_memcpy_blocking(l1_F, l2_F, FC_QKV_SIZE * sizeof(int16_t));
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer weights");

  // On the stack of every core: in L1, all the cores would read the same words
  conv1d_stage_t st[4] = {
      {(mode == TBE) ? im2col_att_tbe : im2col_att_ebt, att, l1_act,
       &l1_F[FC_OUT], y_out, (uint16_t)Embed, (uint16_t)Embed},
      {layernorm_im2col, y_out, l1_act, &l1_F[FC_UP], hidden, (uint16_t)Embed,
       (uint16_t)(2 * Embed)},
      {gelu_im2col, hidden, l1_scratch, &l1_F[FC_DOWN], y,
       (uint16_t)(2 * Embed), (uint16_t)Embed},
      {layernorm_im2col, y, l1_scratch, l1_F, qkv, (uint16_t)Embed,
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
