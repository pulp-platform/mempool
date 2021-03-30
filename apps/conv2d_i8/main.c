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
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/conv_2d.h"

#define M 32
#define N 32
#define KERNEL_N 3
//#define VERBOSE_IN
//#define VERBOSE_OUT

volatile int8_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile uint8_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));
volatile int error __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id, num_cores);

  mempool_barrier(num_cores, num_cores / 2);

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
  mempool_barrier(num_cores, 4 * num_cores);

  return error;
}
