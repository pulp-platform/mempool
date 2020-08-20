// Copyright 2020 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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

#define M 80
#define N (4 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

volatile int32_t in[M * N] __attribute__((section(".l1")));
volatile int32_t out[M * N] __attribute__((section(".l1")));
volatile uint32_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
uint32_t volatile error __attribute__((section(".l1")));

int main(int argc, char **argv) {
  uint32_t core_id = (uint32_t)argc;
  uint32_t num_cores = (uint32_t)argv;
  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    // Hack the allocation of in and out before kernel
    in[0] = -1;
    out[0] = -1;
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

  int tests = error - in[0];

  // Initialize img
  init_conv2d_image(in, N, M, core_id, num_cores);
  // zero_conv2d_image(out, N, M, core_id, num_cores);

#ifdef VERBOSE
  mempool_barrier(core_id, num_cores, num_cores / 4);

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
  for (int i = 0; i < 4; ++i) {
    // Wait at barrier until everyone is ready
    mempool_barrier(core_id, num_cores, num_cores / 2);
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
    mempool_barrier(core_id, num_cores, num_cores * 4);
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
  mempool_barrier(core_id, num_cores, 4 * num_cores);

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

  mempool_barrier(core_id, num_cores, 4 * num_cores);
#endif

  return error;
}
