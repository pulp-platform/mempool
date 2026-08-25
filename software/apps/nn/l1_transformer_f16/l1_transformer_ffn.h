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

void *ffn(__fp16 const *__restrict__ l2_I, __fp16 const *__restrict__ l2_F,
          uint32_t Beam, uint32_t Embed, uint32_t tdSamples, uint32_t Wf) {

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
    dma_memcpy_blocking(F, l2_F, Embed * Embed * 2 * Wf * sizeof(int16_t));
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

  X = T1;
  Y = T2;
  X_im2col = T3;

  mempool_start_benchmark();
  conv1d_f16(X, F, Y, X_im2col, Beam, Embed, Embed * 2, tdSamples, Wf, 1,
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
    __fp16 *GeluIN = &T2[idx * (Embed * 2 * tdSamples)];
    __fp16 *GeluOUT = &T1[idx * (Embed * 2 * tdSamples)];
    softmax_parallel_2x4_f16vec(GeluIN, GeluOUT, Embed * 2, tdSamples,
                                softmax_id, num_cores_per_softmax);
  } else {
    for (uint32_t i = core_id; i < Beam; i += num_cores) {
      __fp16 *GeluIN = &T2[i * (Embed * 2 * tdSamples)];
      __fp16 *GeluOUT = &T1[i * (Embed * 2 * tdSamples)];
      softmax_parallel_2x4_f16vec(GeluIN, GeluOUT, Embed * 2, tdSamples, 0, 1);
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Gelu");

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
  /* Compute convolution on output and sum                                  */
  /**************************************************************************/

  X = T1;
  Y = T2;
  X_im2col = T3;

  mempool_start_benchmark();
  conv1d_f16(X, F, Y, X_im2col, Beam, Embed * 2, Embed, tdSamples, Wf, 1,
             core_id, num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Compute convolution on output");

  return 0;
}
