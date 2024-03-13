// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "baremetal/mempool_conv2d_i8s.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define M 32
#define N 32
#define KERNEL_N 3
// #define VERBOSE_IN
// #define VERBOSE_OUT

volatile int8_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile uint8_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
volatile int error __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Initialize error
    error = 0;
    // Initialize kernel
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
    init_conv2d_image_i8(in, N, M);

#ifdef VERBOSE_IN
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
#endif

    mempool_start_benchmark();
#ifdef __XPULPIMG
    conv2d_3x3_unrolled2_i8_xpulpv2(in, out, M, N, kernel);
#else
    conv2d_3x3_unrolled2_i8_rv32im(in, N, M, kernel, out);
#endif
    mempool_stop_benchmark();

#ifdef VERBOSE_OUT
    printf("out:\n");
    for (int i = 1; i < M - 1; i++) {
      for (int j = 1; j < N - 1; j++) {
        printf("%4u ", out[i * N + j]);
      }
      printf("\n");
    }
#endif

    // verify_conv2d_image_i8_verbose(out, N, M);
    // Check result
    if (verify_conv2d_image_i8(out, N, M)) {
      error = 1;
    }
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
