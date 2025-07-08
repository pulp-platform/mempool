// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_conv2d_f32.h"

#include "baremetal/mempool_conv2d_f32.h"
#include "baremetal/mempool_checks.h"

float in[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
float out[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
float kernel[kernel_K * kernel_K] __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    // Initialize data
    dma_memcpy_blocking(in, l2_A, matrix_M * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(kernel, l2_K, kernel_K * kernel_K * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  // Matrices are initialized --> Start calculating
  mempool_start_benchmark();
  conv2d_3x3_shifted_unrolled_parallel((const float *)in, matrix_N, matrix_M,
                                      (const float *)kernel,
                                      (float *)out, core_id, num_cores);
  mempool_start_benchmark();
  // Wait at barrier befor checking
  mempool_log_barrier(8, core_id);
  mempool_stop_benchmark();

  // Check result
  // mempool_check_f32(out, l2_C, 0, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
