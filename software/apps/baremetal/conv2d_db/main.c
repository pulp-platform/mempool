// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "baremetal/mempool_conv2d_i32p.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Max N is NUM_BANKS * rows that fit L1
#define LOG_RADIX 5
#define M (96)
#define N (4 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

dump(time, 0);

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile int32_t round_barrier[NUM_CORES*BANKING_FACTOR] __attribute__((section(".l1_prio")));
volatile int32_t out_l2[M * N] __attribute__((section(".l2")))
__attribute__((aligned(NUM_CORES * BANKING_FACTOR * 4)));

uint32_t final_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix,
                           uint32_t core_id) {
  uint32_t next_step = step << log2_radix;
  uint32_t barrier_idx = (core_id / next_step) * next_step + step - 1;
  uint32_t *log_barrier = &round_barrier[barrier_idx*BANKING_FACTOR];

  uint32_t val = __atomic_fetch_add(log_barrier, step, __ATOMIC_RELAXED);
  if (val == NUM_CORES - step) {
    // Last core of last stage
    dump_time(2);
    return (uint32_t)log_barrier;
  } else if (val == (uint32_t)(next_step - step)) {
    // Last core of this stage
    __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
    return final_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
  } else {
    if (val == 0 && log_barrier == &round_barrier[0]) {
      dump_time(1);
    }
    // Middle cores, sleep
    mempool_wfi();
  }
  return 0;
}

uint32_t dma_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix, uint32_t core_id) {
  uint32_t next_step = step << log2_radix;
  uint32_t barrier_idx = (core_id / next_step) * next_step + step - 1;
  uint32_t *log_barrier = &round_barrier[barrier_idx*BANKING_FACTOR];

  uint32_t val = __atomic_fetch_add(log_barrier, step, __ATOMIC_RELAXED);
  if (val == NUM_CORES - step) {
    // Last core of last stage
    dump_time(2);
    // Clear wfi that was triggered by the first core
    mempool_wfi();
    return (uint32_t)log_barrier;
  } else if (val == (uint32_t)(next_step - step)) {
    // Last core of this stage
    __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
    return dma_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
  } else if (val == 0 && log_barrier == &round_barrier[0]) {
    // First core of first barrier in first stage
    dump_time(1);
    // Check that the DMA from the previous iteration is done
    dma_wait();
    // Wake up all cores to get to work
    wake_up_all();
    mempool_wfi();
    dump_time(0);
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
  round_barrier[core_id*BANKING_FACTOR] = 0;

  int32_t kernel[KERNEL_N * KERNEL_N];

  kernel[0] = 1;
  kernel[1] = 2;
  kernel[2] = 1;

  kernel[3] = 2;
  kernel[4] = 4;
  kernel[5] = 2;

  kernel[6] = 1;
  kernel[7] = 2;
  kernel[8] = 1;

  // Double-buffered convolution
  const int last_round = 4;
  const uint32_t log2_radix = LOG_RADIX;

  const int32_t *in_comp;
  const int32_t *in_dma;
  int32_t *out_comp;
  int32_t *out_dma;
  uint32_t bar;

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Initialize img
  if (core_id == 0) {
    dma_memcpy_nonblocking((void *)in, (void *)in_l2, M * N / 2 * sizeof(int32_t));
    // Initial launch, Core 0 launched the data transfer
    wake_up_all();
    dump_time(0);
  }

  mempool_start_benchmark();

  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      in_comp = (const int32_t *)&in[0];
      out_comp = (int32_t *)&out[0];
      in_dma = (const int32_t *)&in[N * M / 2];
      out_dma = (int32_t *)&out[N * M / 2];
    } else {
      in_dma = (const int32_t *)&in[0];
      out_dma = (int32_t *)&out[0];
      in_comp = (const int32_t *)&in[N * M / 2];
      out_comp = (int32_t *)&out[N * M / 2];
    }
    mempool_wfi();
    // Barrier, launch DMA for next iteration
    bar = dma_log_barrier(round_barrier, 1, log2_radix, core_id);
    mempool_start_benchmark();
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)in_dma, (void *)in_l2,
                               M * N / 2 * sizeof(int32_t));
      }
      if (round != 0) {
        dma_memcpy_nonblocking((void *)out_l2, (void *)out_dma,
                               M * N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      if (round != last_round - 1) {
        wake_up_all();
      }
    } else {
      // Wait until the core checking the DMA gives the signal
      // mempool_wfi();
    }
    mempool_start_benchmark();
    conv2d_3x3_crazy_parallel((const int32_t *)in_comp, N, M / 2,
                              (const int32_t *)kernel, (int32_t *)out_comp,
                              core_id, NUM_CORES);
    mempool_start_benchmark();
  }

  // Last write back
  bar = final_log_barrier(round_barrier, 1, log2_radix, core_id);
  mempool_start_benchmark();
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking((void *)out_l2, (void *)out_dma,
                        M * N / 2 * sizeof(int32_t));
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    wake_up_all();
    mempool_wfi();
  }

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  return 0;
}
