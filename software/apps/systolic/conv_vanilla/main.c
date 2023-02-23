// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICEDIM_NSE for details.
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

#define DIM_M (20)
#define DIM_N (4 * NUM_CORES)
#define DIM_KERNEL 3
// #define VERBOSE

volatile int32_t in[DIM_M * DIM_N] __attribute__((section(".l1_prio")));
volatile int32_t out[DIM_M * DIM_N] __attribute__((section(".l1_prio")));
volatile uint32_t kernel[DIM_KERNEL * DIM_KERNEL]
    __attribute__((section(".l1")));
volatile int error __attribute__((section(".l1")));


void conv2d_3x3_unrolled_parallel_vanilla(int32_t const *__restrict__ in, uint32_t in_x,
                                          uint32_t in_y, uint32_t const *__restrict__ k,
                                          int32_t volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads) {
  int32_t sum;
  uint32_t weight = 0;
  int32_t local_k[9];
  for (unsigned int i = 0; i < 9; ++i) {
    weight += k[i];
    local_k[i] = (int)k[i];
  }
  // TODO implement boundary halo
  uint32_t div = in_x / numThreads;
  uint32_t rem = in_x % numThreads;
  uint32_t start = div * id;
  uint32_t end = div * (id + 1);
  // Add remainder
  start += id < rem ? id : rem;
  end += id < rem ? id : rem;
  // Now we only care about valid entries
  if (start < 1) {
    start = 1;
  }
  if (end > in_x - 1) {
    end = in_x - 1;
  }

  // Synchronize cores
  mempool_barrier(numThreads);

  for (uint32_t i = start; i < end; ++i) {
    for (uint32_t j = 1; j < in_y - 1; j++) {
      sum = 0;
      sum += in[(j - 1) * in_x + (i - 1)] * local_k[0];
      sum += in[(j - 1) * in_x + (i + 0)] * local_k[1];
      sum += in[(j - 1) * in_x + (i + 1)] * local_k[2];
      sum += in[(j + 0) * in_x + (i - 1)] * local_k[3];
      sum += in[(j + 0) * in_x + (i + 0)] * local_k[4];
      sum += in[(j + 0) * in_x + (i + 1)] * local_k[5];
      sum += in[(j + 1) * in_x + (i - 1)] * local_k[6];
      sum += in[(j + 1) * in_x + (i + 0)] * local_k[7];
      sum += in[(j + 1) * in_x + (i + 1)] * local_k[8];
      out[j * in_x + i] = sum / (int)weight;
    }
  }
}


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
  init_conv2d_image(in, DIM_N, DIM_M, core_id, num_cores);
  // zero_conv2d_image(out, DIM_N, DIM_M, core_id, num_cores);

#ifdef VERBOSE
  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("A:\n");

    for (int i = 0; i < DIM_M; i++) {
      for (int j = 0; j < DIM_N; j++) {
        printf("%4u ", in[i * DIM_N + j]);
      }
      printf("\n");
    }

    printf("kernel:\n");
    for (int i = 0; i < DIM_KERNEL; i++) {
      for (int j = 0; j < DIM_KERNEL; j++) {
        printf("%4u ", kernel[i * DIM_KERNEL + j]);
      }
      printf("\n");
    }
  }

  if (core_id == 0) {
    printf("Start\n");
  }
#endif

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  // Execute benchmark
  mempool_start_benchmark();
  conv2d_3x3_unrolled_parallel_vanilla((const int32_t *)in, DIM_N, DIM_M,
                               (const uint32_t *)kernel, (int32_t *)out,
                               core_id, num_cores);
  mempool_stop_benchmark();
  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  // Check result
  if (verify_conv2d_image(out, DIM_N, DIM_M, core_id, num_cores)) {
    __atomic_fetch_or(&error, 1, __ATOMIC_SEQ_CST);
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
    for (int i = DIM_KERNEL / 2; i < DIM_M - DIM_KERNEL / 2; i++) {
      for (int j = DIM_KERNEL / 2; j < DIM_N - DIM_KERNEL / 2; j++) {
        printf("%4u ", out[i * DIM_N + j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(num_cores);
#endif

  return error;
}
