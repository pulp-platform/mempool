// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "baremetal/mempool_conv2d_i32p.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Max N is NUM_BANKS * rows that fit L1
#define LOG_RADIX 5
#define M (96)
#define N (4 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

dump(time, 0);

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out_l2[M * N] __attribute__((section(".l2")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  int32_t kernel[KERNEL_N * KERNEL_N];

  kernel[0] = 1;
  kernel[1] = 2;
  kernel[2] = 1;

  kernel[3] = 2;
  kernel[4] = 4;
  kernel[5] = 2;

  kernel[6] = 1;
  kernel[7] = 2;
  kernel[8] = 1;

  // Initialize Matrices
  if (core_id == 0) {
    dma_memcpy_blocking((void *)in, (void *)in_l2, M * N * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

  mempool_start_benchmark();
  conv2d_3x3_crazy_parallel((const int32_t *)in, N, M,
                            (const int32_t *)kernel, (int32_t *)out,
                            core_id, NUM_CORES);
  mempool_start_benchmark();
  mempool_log_barrier(8, core_id);
  mempool_start_benchmark();
  conv2d_3x3_crazy_parallel((const int32_t *)in, N, M,
                            (const int32_t *)kernel, (int32_t *)out,
                            core_id, NUM_CORES);
  mempool_start_benchmark();
  mempool_log_barrier(8, core_id);
  mempool_stop_benchmark();

  return 0;
}
