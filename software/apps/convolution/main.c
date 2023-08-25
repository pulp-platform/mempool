// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/convolution.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// #include "convolution_riscv.h"
// #include "halide_runtime.h"

#define M (40)
#define N (3 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

#define CONV2D_PARALLEL                      (0)
#define CONV2D_SHIFTED_PARALLEL              (1)
#define CONV2D_3X3_UNROLLED_PARALLEL         (2)
#define CONV2D_3X3_SHIFTED_UNROLLED_PARALLEL (3)

// Set conv2d version to use
#define CONV_V CONV2D_SHIFTED_PARALLEL

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile uint32_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
volatile int error __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {
#ifdef VERBOSE
    printf("Initialize\n");
#endif
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

#ifdef VERBOSE
  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("A:\n");

    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", in[i * N + j]);
      }
      printf("\n");
    }

    printf("kernel:\n");
    for (int i = 0; i < KERNEL_N; i++) {
      for (int j = 0; j < KERNEL_N; j++) {
        printf("%4u ", kernel[i * KERNEL_N + j]);
      }
      printf("\n");
    }
  }

  if (core_id == 0) {
    printf("Start\n");
  }
#endif

  // Matrices are initialized --> Start calculating
  for (int i = CONV_V; i < CONV_V + 1; ++i) {
    if (core_id == 0) {
      printf("Running ");
      switch (i) {
      case 0:
        printf("conv2d_parallel");
        break;
      case 1:
        printf("conv2d_shifted_parallel");
        break;
      case 2:
        printf("conv2d_3x3_unrolled_parallel");
        break;
      case 3:
        printf("conv2d_3x3_shifted_unrolled_parallel");
        break;
      case 4:
        break;
      }
      printf("...\n");
    }
    // Wait at barrier until everyone is ready
    mempool_barrier(num_cores);
    mempool_start_benchmark();
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
    mempool_stop_benchmark();
    // Wait at barrier befor checking
    mempool_barrier(num_cores);
    // Check result
    if (verify_conv2d_image(out, N, M, core_id, num_cores)) {
      __atomic_fetch_or(&error, i, __ATOMIC_SEQ_CST);
    }
  }

#ifdef VERBOSE
  if (core_id == 0) {
    printf("Done\n");
  }
#endif

  // wait until all cores have finished
  mempool_barrier(num_cores);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("out:\n");
    for (int i = KERNEL_N / 2; i < M - KERNEL_N / 2; i++) {
      for (int j = KERNEL_N / 2; j < N - KERNEL_N / 2; j++) {
        printf("%4u ", out[i * N + j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(num_cores);
#endif

  return error;
}
