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
// a_l2_flat from `data.h`
// b_l2_flat from `data.h`
int32_t matrix_out[matrix_M * matrix_P] __attribute__((section(".l2")))
__attribute__((aligned(NUM_CORES * BANKING_FACTOR * 4)));

uint32_t final_log_barrier(uint32_t step, uint32_t log2_radix,
                           uint32_t core_id) {
  uint32_t *log_barrier =
      (uint32_t *)(((core_id / step) * step + (step >> log2_radix) - 1) *
                   SEQ_MEM_SIZE);

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  // dump_barrier(step * SEQ_MEM_SIZE*SEQ_MEM_SIZE+(uint32_t)log_barrier + val);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES) {
      // Last stage
      // Clear wfi that was triggered by the first core
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return final_log_barrier(step << log2_radix, log2_radix, core_id);
    }
  } else {
    // Middle cores, sleep
    mempool_wfi();
  }
  return 0;
}

uint32_t dma_log_barrier(uint32_t step, uint32_t log2_radix, uint32_t core_id) {
  uint32_t *log_barrier =
      (uint32_t *)(((core_id / step) * step + (step >> log2_radix) - 1) *
                   SEQ_MEM_SIZE);

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  // dump_barrier(step * SEQ_MEM_SIZE*SEQ_MEM_SIZE+(uint32_t)log_barrier + val);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES) {
      // Last stage
      // Clear wfi that was triggered by the first core
      mempool_wfi();
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return dma_log_barrier(step << log2_radix, log2_radix, core_id);
    }
  } else if (val == 0 && (uint32_t)log_barrier == 0) {
    // First core of first barrier in first stage
    // Check that the DMA from the previous iteration is done
    dma_wait();
    // Wake up all cores to get to work
    wake_up_all();
    mempool_wfi();
  } else {
    // Middle cores, sleep
    mempool_wfi();
  }
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  // Initial setup
  int32_t *round_barrier = (int32_t *)(core_id * SEQ_MEM_SIZE);
  if (core_id != 0) {
    *round_barrier = 0;
  }

  // Initialize img
  if (core_id == 0) {
    dma_memcpy_nonblocking((void *)matrix_a1, (void *)a_l2_flat,
                           matrix_M * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking((void *)matrix_b1, (void *)b_l2_flat,
                        matrix_N * matrix_P * sizeof(int32_t));
  }

  // Double-buffered convolution
  const int last_round = 4;
  // const int first = 0;
  const uint32_t log2_radix = 4;
  const uint32_t radix = 1 << log2_radix;
  const uint32_t last = radix - 1; // Radix 4 barrier

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Initial launch, Core 0 transfered the data in
  if (core_id == 0) {
    wake_up_all();
  }
  const int32_t *a_comp;
  const int32_t *b_comp;
  const int32_t *a_dma;
  const int32_t *b_dma;
  uint32_t bar;

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
    mempool_wfi();
    // Barrier, launch DMA for next iteration
    bar = dma_log_barrier(radix, log2_radix, core_id);
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)a_dma, (void *)a_l2_flat,
                               matrix_M * matrix_N * sizeof(int32_t));
        dma_memcpy_nonblocking((void *)b_dma, (void *)b_l2_flat,
                               matrix_N * matrix_P * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      if (round != last_round - 1) {
        wake_up_all();
      }
    }
    mempool_stop_benchmark();
    mempool_start_benchmark();
    mat_mul_unrolled_4x4_parallel_asm(a_comp, b_comp, matrix_c, matrix_M, matrix_N, matrix_P, core_id,
                                      num_cores);
    mempool_stop_benchmark();
  }

  // Last write back
  mempool_start_benchmark();
  bar = final_log_barrier(radix, log2_radix, core_id);
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking((void *)matrix_out, (void *)matrix_c,
                        matrix_M * matrix_P * sizeof(int32_t));
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    wake_up_all();
  }

  mempool_stop_benchmark();

  return 0;
}
