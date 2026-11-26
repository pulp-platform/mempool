// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_conv1d_f16.h"
#include "data_conv1d_f16.h"

#define IM2COL (1)

__fp16 l1_X[matrix_B * matrix_Ci * matrix_Wi]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_Xim2col[matrix_B * matrix_Ci * matrix_Wi * matrix_Wf]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_F[matrix_Co * matrix_Ci * matrix_Wf]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_Y[matrix_B * matrix_Co * matrix_Wi]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

__fp16 l2_Z[matrix_B * matrix_Co * matrix_Wi]
    __attribute__((aligned(sizeof(int32_t)), section(".l2"))) = {0};

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  /* Initialize barrier */
  mempool_barrier_init(core_id);

  /* DMA input tensors to L1 */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_Y, l2_Z,
                        matrix_B * matrix_Co * matrix_Wi * sizeof(__fp16));
    dma_memcpy_blocking(l1_X, l2_X,
                        matrix_B * matrix_Ci * matrix_Wi * sizeof(__fp16));
    dma_memcpy_blocking(l1_F, l2_F,
                        matrix_Co * matrix_Ci * matrix_Wf * sizeof(__fp16));
  }
  mempool_barrier(num_cores);

  /* Run convolution (single core reference) */
  mempool_start_benchmark();
  conv1d_f16(l1_X, l1_F, l1_Y, l1_Xim2col, matrix_B, matrix_Ci, matrix_Co,
             matrix_Wi, matrix_Wf, IM2COL, core_id, num_cores);
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  /* Check results */
  mempool_check_f16(l1_Y, l2_Y, matrix_B * matrix_Co * matrix_Wi, 0.5f, 0);
  mempool_barrier(num_cores);
  return 0;
}
