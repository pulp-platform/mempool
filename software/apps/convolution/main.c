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

#define M (96)
#define N (4 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

dump(time, 0);

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
// volatile int32_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
volatile int error __attribute__((section(".l2")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  int32_t kernel[KERNEL_N * KERNEL_N];

  if (core_id == 0) {
#ifdef VERBOSE
    printf("Initialize\n");
#endif
    error = 0;
  }

  kernel[0] = 1;
  kernel[1] = 2;
  kernel[2] = 1;

  kernel[3] = 2;
  kernel[4] = 4;
  kernel[5] = 2;

  kernel[6] = 1;
  kernel[7] = 2;
  kernel[8] = 1;

  // Initialize img
  init_conv2d_image(in, N, M, core_id, num_cores);
  // zero_conv2d_image(out, N, M, core_id, num_cores);

  // #ifdef VERBOSE
  //   mempool_barrier(num_cores);

  //   if (core_id == 0) {
  //     printf("A:\n");

  //     for (int i = 0; i < M; i++) {
  //       for (int j = 0; j < N; j++) {
  //         printf("%4u ", in[i * N + j]);
  //       }
  //       printf("\n");
  //     }

  //     printf("kernel:\n");
  //     for (int i = 0; i < KERNEL_N; i++) {
  //       for (int j = 0; j < KERNEL_N; j++) {
  //         printf("%4u ", kernel[i * KERNEL_N + j]);
  //       }
  //       printf("\n");
  //     }
  //   }

  //   if (core_id == 0) {
  //     printf("Start\n");
  //   }
  // #endif

  // Matrices are initialized --> Start calculating
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  uint32_t start = mempool_get_timer();
  mempool_start_benchmark();
  conv2d_3x3_crazy_parallel((const int32_t *)in, N, M, (const int32_t *)kernel,
                            (int32_t *)out, core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  uint32_t stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

  // Hot cache
  start = mempool_get_timer();
  mempool_start_benchmark();
  conv2d_3x3_crazy_parallel((const int32_t *)in, N, M, (const int32_t *)kernel,
                            (int32_t *)out, core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

  // Check result
  if (verify_conv2d_image(out, N, M, core_id, num_cores)) {
    error = 1;
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("Done (Error=%d)\n", error);
  }
#endif

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
