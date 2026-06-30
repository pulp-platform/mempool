// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "baremetal/mempool_conv1d_f16.h"

void *layernorm_conv1d(__fp16 const *__restrict__ l2_F,
                       __fp16 const *__restrict__ l2_b, __fp16 *__restrict__ X,
                       __fp16 *__restrict__ Y, uint32_t Batch, uint32_t Ci,
                       uint32_t Co, uint32_t Wi, uint32_t Wf) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  static __fp16 *F = l1_F;   // Should be allocated dinamically
  static __fp16 *T1 = l1_T1; // Should be allocated dinamically

  // Transfer weights

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, Co * Ci * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Convolution

  conv1d_f16(T1, F, Y, l1_X_im2col,
    Batch, Ci, Co, Wi, Wf, IM2COL, core_id, num_cores);

  // Layer Normalization

  mempool_start_benchmark();
  uint32_t num_cores_per_batch = num_cores / Batch;
  uint32_t batch_id = core_id % num_cores_per_batch;
  uint32_t idx = core_id / num_cores_per_batch;
  __fp16 *X_ptr = &X[idx * Ci * Wi];
  __fp16 *T1_ptr = &T1[idx * Ci * Wi];
  layernorm_parallel_2x4_f16vec(X_ptr, T1_ptr,
    Ci, Wi, batch_id, num_cores_per_batch);
  mempool_stop_benchmark();

  // Transfer weights

  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(F, l2_F, Co * Ci * Wf * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Convolution

  conv1d_f16(T1, F, Y, l1_X_im2col,
    Batch, Ci, Co, Wi, Wf, IM2COL, core_id, num_cores);

  return Y;
}
