// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "kernel/axpy.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N (1024 * 96)

dump(time, 0);

int32_t vec_x[N] __attribute__((section(".l1_prio")));
int32_t vec_y[N] __attribute__((section(".l1_prio")));

// vec_x_l2_flat from `data.h`
// vec_y_l2_flat from `data.h`
int32_t vec_y_l2_out[N] __attribute__((section(".l2")))
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
      dump_time(2);
      // Clear wfi that was triggered by the first core
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return final_log_barrier(step << log2_radix, log2_radix, core_id);
    }
  } else {
    if (val == 0 && (uint32_t)log_barrier == 0)
      dump_time(1);
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
      dump_time(2);
      // Clear wfi that was triggered by the first core
      mempool_wfi();
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return dma_log_barrier(step << log2_radix, log2_radix, core_id);
    }
  } else if (val == 0 && (uint32_t)log_barrier == 0) {
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
  int32_t *round_barrier = (int32_t *)(core_id * SEQ_MEM_SIZE);
  if (core_id != 0) {
    *round_barrier = 0;
  }

  // Initialize img
  if (core_id == 0) {
    dma_memcpy_nonblocking((void *)vec_x, (void *)vec_x_l2_flat,
                           N / 2 * sizeof(int32_t));
    dma_memcpy_blocking((void *)vec_y, (void *)vec_y_l2_flat,
                        N / 2 * sizeof(int32_t));
  }

  // Double-buffered convolution
  const int last_round = 4;
  // const int first = 0;
  const uint32_t log2_radix = 4;
  const uint32_t radix = 1 << log2_radix;

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Initial launch, Core 0 transfered the data in
  if (core_id == 0) {
    wake_up_all();
  }
  const int32_t *vec_x_comp;
  const int32_t *vec_x_dma;
  const int32_t *vec_y_comp;
  const int32_t *vec_y_dma;

  const int32_t *vec_x_in;
  const int32_t *vec_y_in;
  const int32_t *vec_y_out;
  uint32_t bar;

  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      vec_x_comp = (const int32_t *)&vec_x[0];
      vec_x_dma = (const int32_t *)&vec_x[N / 2];
      vec_y_comp = (const int32_t *)&vec_y[0];
      vec_y_dma = (const int32_t *)&vec_y[N / 2];

      vec_x_in = (const int32_t *)&vec_x_l2_flat[N / 2];
      vec_y_in = (const int32_t *)&vec_y_l2_flat[N / 2];
      vec_y_out = (const int32_t *)&vec_y_l2_out[N / 2];
    } else {
      vec_x_comp = (const int32_t *)&vec_x[N / 2];
      vec_x_dma = (const int32_t *)&vec_x[0];
      vec_y_comp = (const int32_t *)&vec_y[N / 2];
      vec_y_dma = (const int32_t *)&vec_y[0];

      vec_x_in = (const int32_t *)&vec_x_l2_flat[0];
      vec_y_in = (const int32_t *)&vec_y_l2_flat[0];
      vec_y_out = (const int32_t *)&vec_y_l2_out[0];
    }
    mempool_start_benchmark();
    mempool_wfi();
    // Barrier, launch DMA for next iteration
    bar = dma_log_barrier(radix, log2_radix, core_id);
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != 0) {
        dma_memcpy_nonblocking((void *)vec_y_out, (void *)vec_y_dma,
                               N / 2 * sizeof(int32_t));
      }
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)vec_x_dma, (void *)vec_x_in,
                               N / 2 * sizeof(int32_t));
        dma_memcpy_nonblocking((void *)vec_y_dma, (void *)vec_y_in,
                               N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      if (round != last_round - 1) {
        wake_up_all();
      }
    }
    mempool_stop_benchmark();
    mempool_start_benchmark();
    axpy_parallel_asm((const int32_t *)vec_x_comp, (int32_t *)vec_y_comp, 7,
                      N / 2, core_id, num_cores);
    mempool_stop_benchmark();
  }

  // Last write back
  mempool_start_benchmark();
  bar = final_log_barrier(radix, log2_radix, core_id);
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking((void *)vec_y_out, (void *)vec_y_dma,
                        N / 2 * sizeof(int32_t));
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    wake_up_all();
  }

  mempool_stop_benchmark();

  return 0;
}
