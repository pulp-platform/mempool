// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "kernel/dct.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// #include "convolution_riscv.h"
// #include "halide_runtime.h"

#define M (8 * 24)
#define N (4 * NUM_CORES)
// #define VERBOSE

// img_l2_flat defined in `data.h`
volatile int32_t img_l1[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out_l2[M * N] __attribute__((section(".l2")))
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
    dma_memcpy_blocking((void *)img_l1, (void *)img_l2_flat,
                        M * N / 2 * sizeof(int32_t));
  }

#ifdef VERBOSE
  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("In:\n");

    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", img_l1[i * N + j]);
      }
      printf("\n");
    }
  }
#endif

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
  const int32_t *img_comp;
  const int32_t *img_dma;
  const int32_t *in_dma;
  const int32_t *out_dma;
  uint32_t bar;

  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      img_comp = (const int32_t *)&img_l1[0];
      img_dma = (const int32_t *)&img_l1[N * M / 2];
      in_dma = (const int32_t *)&img_l2_flat[N * M / 2];
      out_dma = (const int32_t *)&out_l2[N * M / 2];
    } else {
      img_comp = (const int32_t *)&img_l1[N * M / 2];
      img_dma = (const int32_t *)&img_l1[0];
      in_dma = (const int32_t *)&img_l2_flat[0];
      out_dma = (const int32_t *)&out_l2[0];
    }
    mempool_start_benchmark();
    mempool_wfi();
    // Barrier, launch DMA for next iteration
    bar = dma_log_barrier(radix, log2_radix, core_id);
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != 0) {
        dma_memcpy_nonblocking((void *)out_dma, (void *)img_dma,
                               M * N / 2 * sizeof(int32_t));
      }
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)img_dma, (void *)in_dma,
                               M * N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      if (round != last_round - 1) {
        wake_up_all();
      }
    }
    mempool_stop_benchmark();
    mempool_start_benchmark();
    fdct_8x8_parallel((const int32_t *)img_comp, N, M / 2, (int32_t *)img_comp,
                      core_id, num_cores);
    mempool_stop_benchmark();
  }

  // Last write back
  mempool_start_benchmark();
  bar = final_log_barrier(radix, log2_radix, core_id);
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking((void *)out_dma, (void *)img_dma,
                        M * N / 2 * sizeof(int32_t));
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    wake_up_all();
  }

  mempool_stop_benchmark();

#ifdef VERBOSE
  if (core_id == 0) {
    printf("img_l1:\n");
    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", img_l1[i * N + j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(num_cores);
#endif

  return 0;
}
