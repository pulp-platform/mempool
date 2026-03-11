// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "baremetal/mempool_dct_i32p.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// #include "convolution_riscv.h"
// #include "halide_runtime.h"

#define M (8 * 8)
#define N (4 * NUM_CORES)
// #define VERBOSE

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int error __attribute__((section(".l1")));

void init_img(volatile int32_t *img, uint32_t size, uint32_t core_id,
              uint32_t num_cores) {
  for (uint32_t i = core_id; i < size; i += num_cores) {
    img[i] = (int32_t)i;
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

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
  mempool_barrier(num_cores);

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
  mempool_barrier(num_cores);
  mempool_start_benchmark();
  fdct_8x8_parallel((int32_t *)in, N, M, (int32_t *)in, core_id, num_cores);
  mempool_stop_benchmark();
  // Wait at barrier befor checking
  mempool_barrier(num_cores);

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

  mempool_barrier(num_cores);
#endif

  return error;
}
