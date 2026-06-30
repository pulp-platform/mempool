// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "dma.h"
#include "hal_redmule.h"

#include "baremetal/mempool_softmax_f16.h"
#include "l1_transformer_conv1d.h"
#include "l1_transformer_print.h"

void *ffn(__fp16 const *__restrict__ l2_I, __fp16 const *__restrict__ l2_F,
          __fp16 const *__restrict__ l2_b, uint32_t Beam, uint32_t Embed,
          uint32_t tdSamples, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  static __fp16 *I = l1_I;   // Should be allocated dinamically
  static __fp16 *T1 = l1_T1; // Should be allocated dinamically
  static __fp16 *T2 = l1_T2; // Should be allocated dinamically
  static __fp16 *F = l1_F; // Should be allocated dinamically
  static __fp16 *b = l1_b; // Should be allocated dinamically

  /**************************************************************************/
  /* Transfer inputs                                                        */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(I, l2_I, Embed * Beam * tdSamples * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer inputs");

  /**************************************************************************/
  /* Conv1D block                                                           */
  /**************************************************************************/

#if defined(COMPUTE)
  layernorm_conv1d(l2_F, l2_b, I, T2, Beam, Embed, Embed * 2, tdSamples, Wf);
#endif

  PRINT_DONE(VERBOSE, core_id, num_cores, "Convolution and layernorm");

  /**************************************************************************/
  /* Transfer weights                                                       */
  /**************************************************************************/

  if (core_id == 0) {
    dma_memcpy_nonblocking(F, l2_F, Embed * Embed * Wf * sizeof(int16_t));
    dma_memcpy_nonblocking(b, l2_b, Embed * sizeof(int16_t));
  }

  PRINT_DONE(VERBOSE, core_id, num_cores, "Transfer weights");

  /**************************************************************************/
  /* Gelu                                                                   */
  /**************************************************************************/

#if defined(COMPUTE)
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
  mempool_stop_benchmark();
#endif

  PRINT_DONE(VERBOSE, core_id, num_cores, "Gelu");

  /**************************************************************************/
  /* Synchronize and wait for weights transfer end                          */
  /**************************************************************************/

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_wait();
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  PRINT_DONE(VERBOSE, core_id, num_cores, "Synchronize and wait for weights");

  /**************************************************************************/
  /* Compute convolution on output and sum                                  */
  /**************************************************************************/

#if defined(COMPUTE)
  mempool_start_benchmark();
  conv1d_f16(T1, F, I, l1_X_im2col, Beam, Embed * 2, Embed, tdSamples, Wf,
             IM2COL, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  PRINT_DONE(VERBOSE, core_id, num_cores, "Compute convolution on output");

  mempool_barrier(num_cores);
  return T2;
}
