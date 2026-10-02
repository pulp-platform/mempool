// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_conv1d_f16.h"
#ifdef PIPELINED
#include "baremetal/mempool_gelu_f16.h"
#endif
#include "baremetal/mempool_layernorm_f16.h"
#include "baremetal/mempool_softmax_f16.h"

/**
  @brief         Computes the feed-forward block.
  @param[in]     l2_I      Input tensor in L2 memory, used when in is NULL
  @param[in]     l2_F      Convolution filter weights in L2 memory
  @param[in]     in        Output of the previous layer in L1, or NULL
  @return        Output of the layer in L1, [Beam][Embed][tdSamples]
*/

__fp16 *ffn(__fp16 const *__restrict__ l2_I, __fp16 const *__restrict__ l2_F,
            __fp16 const *in, uint32_t Beam, uint32_t Embed,
            uint32_t tdSamples, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Data of this layer and the L1 buffer that holds it (see l2_data.h). A
  // buffer is reused once nothing reads its previous content any more.
  //   x       input [Beam][Embed][tdSamples]     l1_arena.x
  //   x_norm  layernorm output                   l1_act
  //   cols    im2col of the convolutions         l1_scratch
  //   up      up-projection [Beam][2*Embed][..]  l1_arena.y      over x
  //   hidden  Gelu of up                         PIPELINED: in place on up,
  //                                              else l1_act over x_norm
  //   y       output [Beam][Embed][tdSamples]    PIPELINED: l1_act over x_norm,
  //                                              else l1_arena.y over up
  __fp16 *x = l1_arena.x;
  __fp16 *x_norm = l1_act;
  __fp16 *cols = l1_scratch;
  __fp16 *up = l1_arena.y;
#ifdef PIPELINED
  __fp16 *hidden = up;
  __fp16 *y = l1_act;
#else
  __fp16 *hidden = l1_act;
  __fp16 *y = l1_arena.y;
#endif
  __fp16 *F = l1_F;

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
    dma_memcpy_blocking(F, l2_F, F_BYTES(Embed * Embed * 2 * Wf));
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

#ifdef PIPELINED
  /**************************************************************************/
  /* Conv1D + Gelu                                                          */
  /**************************************************************************/

  // Convolution: up-projection (Embed -> 2*Embed), Gelu applied in place
  mempool_start_benchmark();
  conv1d_pipelined_f16(x_norm, F, F_STRIDE, up, cols, Beam, Embed, Embed * 2,
                       tdSamples, Wf, gelu_f16, core_id, num_cores);
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

  mempool_start_benchmark();
  if (Beam < num_cores) {
    uint32_t num_cores_per_softmax = num_cores / Beam;
    uint32_t softmax_id = core_id % num_cores_per_softmax;
    uint32_t idx = core_id / num_cores_per_softmax;
    softmax_parallel_2x4_f16vec(&up[idx * (Embed * 2 * tdSamples)],
                                &hidden[idx * (Embed * 2 * tdSamples)],
                                Embed * 2, tdSamples, softmax_id,
                                num_cores_per_softmax);
  } else {
    for (uint32_t i = core_id; i < Beam; i += num_cores) {
      softmax_parallel_2x4_f16vec(&up[i * (Embed * 2 * tdSamples)],
                                  &hidden[i * (Embed * 2 * tdSamples)],
                                  Embed * 2, tdSamples, 0, 1);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Gelu");
#endif

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, F_BYTES(Embed * Embed * Wf));
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
  conv1d_pipelined_f16(hidden, F, F_STRIDE, y, cols, Beam, Embed * 2, Embed,
                       tdSamples, Wf, NULL, core_id, num_cores);
#else
  conv1d_f16(hidden, F, y, cols, Beam, Embed * 2, Embed, tdSamples, Wf, 1,
             core_id, num_cores);
#endif
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Compute convolution on output");

  return y;
}
