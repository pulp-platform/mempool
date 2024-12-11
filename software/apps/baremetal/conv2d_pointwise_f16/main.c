// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_conv2d_f16.h"
#include "data_conv2d_pointwise_f16.h"

__fp16 l1_A[matrix_M * matrix_N * matrix_D]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_B[matrix_M * matrix_N * kernel_D]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[matrix_D * kernel_D]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices 1
  if (core_id == 0) {
    dma_memcpy_blocking(l1_A, l2_A,
                        (matrix_M * matrix_N * matrix_D) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (matrix_D * kernel_D) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    conv2d_pointwise_f16s_unrolled4(l1_A, l1_B, l1_W, matrix_M, matrix_N,
                                    matrix_D, kernel_D);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  mempool_check_f16(l1_B, l2_B, matrix_M * matrix_N * kernel_D, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
