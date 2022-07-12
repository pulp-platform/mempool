// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "kernel/mat_mul.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]
#if NUM_CORES > 32
#define matrix_M 192
#define matrix_N 192
#define matrix_P 192
#else
#define matrix_M (NUM_CORES)
#define matrix_N (NUM_CORES)
#define matrix_P (NUM_CORES)
#endif

int32_t matrix_a1[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
int32_t matrix_a2[matrix_M * matrix_N] __attribute__((section(".l1_prio")));
int32_t matrix_b1[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
int32_t matrix_b2[matrix_N * matrix_P] __attribute__((section(".l1_prio")));
int32_t matrix_c[matrix_M * matrix_P] __attribute__((section(".l1_prio")));

dump(time, 0);

int test_matrix_multiplication(int32_t *__restrict__ A, int32_t *__restrict__ B,
                               int32_t *__restrict__ C, uint32_t M, uint32_t N,
                               uint32_t P, uint32_t core_id,
                               uint32_t num_cores) {

  if (core_id == 0) {
    dma_memcpy_blocking((void *)matrix_a1, (void *)A, M * N * sizeof(int32_t));
    dma_memcpy_blocking((void *)matrix_b1, (void *)B, N * P * sizeof(int32_t));
  }
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

  // Double-buffered convolution
  int last_round = 6;
  int first = 0;
  int last = 2 * (int)num_cores;
  int32_t *round_barrier = (int32_t *)(64 * 1024);

  // Initial setup
  if (core_id == 0) {
    *round_barrier = 0;
    wake_up_all();
  }

  const int32_t *a_comp;
  const int32_t *b_comp;
  const int32_t *a_dma;
  const int32_t *b_dma;
  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      a_comp = (const int32_t *)matrix_a1;
      b_comp = (const int32_t *)matrix_b1;
      a_dma = (const int32_t *)matrix_a2;
      b_dma = (const int32_t *)matrix_b2;
    } else {
      a_dma = (const int32_t *)matrix_a1;
      b_dma = (const int32_t *)matrix_b1;
      a_comp = (const int32_t *)matrix_a2;
      b_comp = (const int32_t *)matrix_b2;
    }
    mempool_start_benchmark();
    // Barrier, launch DMA for next iteration
    mempool_wfi();
    int bar = __atomic_fetch_add(round_barrier, 2, __ATOMIC_RELAXED);
    // Are we the first to reach the next round?
    if (bar == first) {
      dma_wait();
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)a_dma, (void *)A,
                               M * N * sizeof(int32_t));
        dma_memcpy_nonblocking((void *)b_dma, (void *)B,
                               N * P * sizeof(int32_t));
      }
      // TODO add copy out
      bar = __atomic_fetch_add(round_barrier, 2, __ATOMIC_RELAXED);
    }
    // Are we the last one?
    if (bar == last) {
      *round_barrier = 0;
      if (round != last_round - 1) {
        wake_up_all();
      }
    }

    mempool_stop_benchmark();
    mempool_start_benchmark();
    mat_mul_unrolled_4x4_parallel_asm(a_comp, b_comp, C, M, N, P, core_id,
                                      num_cores);
    mempool_stop_benchmark();
  }

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Test the Matrix multiplication
  test_matrix_multiplication(a_l2_flat, b_l2_flat, matrix_c, matrix_M, matrix_N,
                             matrix_P, core_id, num_cores);

  // return error;
  return 0;
}
