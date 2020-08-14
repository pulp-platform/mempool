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

#define M 4
#define N 4
#define KERNEL_N 3
#define VERBOSE

int32_t volatile in[M * N] __attribute__((section(".l1")));
int32_t volatile out[M * N] __attribute__((section(".l1")));
uint32_t volatile kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));

int check_out(int32_t *out) {
  uint32_t error = 0;
  for (int i = 0; i < N * M; ++i) {
    if (out[i] == 0)
      error += 1;
    out[i] = 0;
  }
  return 0;
}

int main(int argc, char **argv) {
  uint32_t core_id = (uint32_t)argc;
  uint32_t num_cores = (uint32_t)argv;
  mempool_barrier_init(core_id, num_cores);

  // #ifdef VERBOSE
  if (core_id == 0) {
    printf("Initialize\n");
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
  // #endif

  // Initialize in
  for (int i = core_id; i < M; i += num_cores) {
    for (int j = 0; j < N; j++) {
      in[i * N + j] = core_id + ((i * i) + 4 * (j % 3) + (j % 9)) % 128;
    }
  }

  mempool_barrier(core_id, num_cores, num_cores / 4);

#ifdef VERBOSE
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

  mempool_barrier(core_id, num_cores, num_cores / 4);

  if (core_id == 0) {
    printf("Start\n");
  }
#endif

  if (core_id == 0) {
    conv2d_3x3_shifted_unrolled(in, N, M, kernel, out);
  }

  // // Initialized --> Start calculating
  // conv2d_shifted_parallel(in, N, M, kernel, KERNEL_N, KERNEL_N, out, core_id,
  //                 num_cores);
  // // check_out(out);

  // // wait until all cores have finished
  // mempool_barrier(core_id, num_cores, num_cores / 4);

  // // Initialized --> Start calculating
  // conv2d_3x3_unrolled_parallel(in, N, M, kernel, out, core_id, num_cores);
  // // check_out(out);

  // // wait until all cores have finished
  // mempool_barrier(core_id, num_cores, num_cores / 4);

  // conv2d_3x3_shifted_unrolled_parallel(in, N, M, kernel, out, core_id,
  //                                      num_cores);
  // // check_out(out);

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

  return 0;
}
