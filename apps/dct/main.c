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
#include "kernel/dct.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// #include "convolution_riscv.h"
// #include "halide_runtime.h"

#define M (8 * 2 * 8)
#define N (4 * NUM_CORES)
// #define VERBOSE

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile uint32_t error __attribute__((section(".l1")));

void init_img(volatile int32_t *img, uint32_t size, uint32_t core_id,
              uint32_t num_cores) {
  for (uint32_t i = core_id; i < size; i += num_cores) {
    img[i] = (int32_t)i;
  }
}

int main(int argc, char **argv) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id, num_cores);

  if (core_id == 0) {
    // Hack the allocation of in and out before kernel
    in[0] = -1;
#ifdef VERBOSE
    printf("Initialize\n");
#endif
    error = 0;
  }

  // Initialize img
  init_img(in, M * N, core_id, num_cores);

#ifdef VERBOSE
  mempool_barrier(core_id, num_cores, num_cores / 4);

  if (core_id == 0) {
    printf("In:\n");

    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", in[i * N + j]);
      }
      printf("\n");
    }
  }
#endif

  // Wait at barrier until everyone is ready
  mempool_barrier(core_id, num_cores, num_cores / 2);
  mempool_start_benchmark();
  fdct_8x8_parallel(in, N, M, in, core_id, num_cores);
  mempool_stop_benchmark();
  // Wait at barrier befor checking
  mempool_barrier(core_id, num_cores, num_cores * 4);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("in:\n");
    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", in[i * N + j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(core_id, num_cores, 4 * num_cores);
#endif

  return error;
}
