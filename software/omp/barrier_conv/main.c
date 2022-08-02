// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/convolution.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define M (20)
#define N (4 * NUM_CORES)
#define KERNEL_N 3
#define WAIT_BARRIER (2 * NUM_CORES)

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile uint32_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
volatile int error __attribute__((section(".l1")));

void conv_mempool_barrier(uint32_t core_id, uint32_t num_cores) {
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
    kernel[0] = 1;
    kernel[1] = 2;
    kernel[2] = 1;

    kernel[3] = 2;
    kernel[4] = 4;
    kernel[5] = 2;

    kernel[6] = 1;
    kernel[7] = 2;
    kernel[8] = 1;
  }

  // Initialize img
  init_conv2d_image(in, N, M, core_id, num_cores);
  // zero_conv2d_image(out, N, M, core_id, num_cores);

  // Matrices are initialized --> Start calculating
  for (int i = 2; i < 3; ++i) {
    // Wait at barrier until everyone is ready
    mempool_barrier(num_cores);

    switch (i) {
    case 0:
      conv2d_parallel((const int32_t *)in, N, M, (const uint32_t *)kernel,
                      KERNEL_N, KERNEL_N, (int32_t *)out, core_id, num_cores);
      break;
    case 1:
      conv2d_shifted_parallel((const int32_t *)in, N, M,
                              (const uint32_t *)kernel, KERNEL_N, KERNEL_N,
                              (int32_t *)out, core_id, num_cores);
      break;
    case 2:
      conv2d_3x3_unrolled_parallel((const int32_t *)in, N, M,
                                   (const uint32_t *)kernel, (int32_t *)out,
                                   core_id, num_cores);
      break;
    case 3:
      conv2d_3x3_shifted_unrolled_parallel((const int32_t *)in, N, M,
                                           (const uint32_t *)kernel,
                                           (int32_t *)out, core_id, num_cores);
      break;
    case 4:
      break;
    }

    // Wait at barrier befor checking
    mempool_barrier(num_cores);

    // Check result
    if (verify_conv2d_image(out, N, M, core_id, num_cores)) {
      __atomic_fetch_or(&error, i, __ATOMIC_SEQ_CST);
    }
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
}

void conv_gomp_barrier(uint32_t core_id, uint32_t num_cores) {

  if (core_id == 0) {
    error = 0;
    kernel[0] = 1;
    kernel[1] = 2;
    kernel[2] = 1;

    kernel[3] = 2;
    kernel[4] = 4;
    kernel[5] = 2;

    kernel[6] = 1;
    kernel[7] = 2;
    kernel[8] = 1;
  }

  // Initialize img
  init_conv2d_image(in, N, M, core_id, num_cores);
  // zero_conv2d_image(out, N, M, core_id, num_cores);

  // Matrices are initialized --> Start calculating
  for (int i = 2; i < 3; ++i) {
// Wait at barrier until everyone is ready
#pragma omp barrier

    switch (i) {
    case 0:
      conv2d_parallel((const int32_t *)in, N, M, (const uint32_t *)kernel,
                      KERNEL_N, KERNEL_N, (int32_t *)out, core_id, num_cores);
      break;
    case 1:
      conv2d_shifted_parallel((const int32_t *)in, N, M,
                              (const uint32_t *)kernel, KERNEL_N, KERNEL_N,
                              (int32_t *)out, core_id, num_cores);
      break;
    case 2:
      conv2d_3x3_unrolled_parallel((const int32_t *)in, N, M,
                                   (const uint32_t *)kernel, (int32_t *)out,
                                   core_id, num_cores);
      break;
    case 3:
      conv2d_3x3_shifted_unrolled_parallel((const int32_t *)in, N, M,
                                           (const uint32_t *)kernel,
                                           (int32_t *)out, core_id, num_cores);
      break;
    case 4:
      break;
    }

// Wait at barrier befor checking
#pragma omp barrier
    // Check result
    if (verify_conv2d_image(out, N, M, core_id, num_cores)) {
      __atomic_fetch_or(&error, i, __ATOMIC_SEQ_CST);
    }
  }

// wait until all cores have finished
#pragma omp barrier
}

int main() {
  mempool_timer_t cycles, start_time;
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  if (core_id == 0) {
    printf("Start Barrier Benchmark\n");
  }

#pragma omp barrier
  start_time = mempool_get_timer();
  mempool_start_benchmark();
  conv_mempool_barrier(core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer();

  if (core_id == 0) {
    printf("Mempool barrier cycles: %d\n", cycles - start_time);
  }

  mempool_barrier(num_cores);

  start_time = mempool_get_timer();
  mempool_start_benchmark();
  conv_gomp_barrier(core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer();

  if (core_id == 0) {
    printf("GOMP barrier cycles: %d\n", cycles - start_time);
  }

#pragma omp barrier
  return 0;
}
