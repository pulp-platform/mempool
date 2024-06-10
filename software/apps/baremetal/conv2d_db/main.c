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

// Max N is NUM_BANKS_PER_CLUSTER * rows that fit L1
#if NUM_CORES_PER_CLUSTER == 16
#define LOG_RADIX 2
#elif NUM_CORES_PER_CLUSTER == 32
#define LOG_RADIX 3
#elif NUM_CORES_PER_CLUSTER == 64
#define LOG_RADIX 3
#elif NUM_CORES_PER_CLUSTER == 128
#define LOG_RADIX 4
#elif NUM_CORES_PER_CLUSTER == 256
#define LOG_RADIX 4
#endif

#define M (92)
#define N (4 * NUM_CORES_PER_CLUSTER)
#define KERNEL_N 3
// #define VERBOSE

dump(time, 0);

volatile int32_t out_l2[M * N] __attribute__((section(".l2")))
__attribute__((aligned(NUM_CORES * BANKING_FACTOR * 4)));

uint32_t final_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix,
                           uint32_t core_id) {
  uint32_t next_step = step << log2_radix;
  uint32_t barrier_idx = (core_id / next_step) * next_step + step - 1;
  uint32_t *log_barrier = &round_barrier[barrier_idx*BANKING_FACTOR];

  uint32_t val = __atomic_fetch_add(log_barrier, step, __ATOMIC_RELAXED);
  if (val == NUM_CORES_PER_CLUSTER - step) {
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
  if (val == NUM_CORES_PER_CLUSTER - step) {
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
    uint32_t cluster_id = mempool_get_core_id()/NUM_CORES_PER_CLUSTER;
    dma_wait(cluster_id);
    // Wake up all cores to get to work
    wake_up_cluster(cluster_id);
    mempool_wfi();
    dump_time(0);
  } else {
    // Middle cores, sleep
    mempool_wfi();
  }
  return 0;
}

uint32_t hard_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix, uint32_t core_id) {
  uint32_t next_step = step << log2_radix;
  uint32_t barrier_idx = (core_id / next_step) * next_step + step - 1;
  uint32_t *log_barrier = &round_barrier[barrier_idx*BANKING_FACTOR];

  uint32_t val = __atomic_fetch_add(log_barrier, step, __ATOMIC_RELAXED);
  if (val == NUM_CORES_PER_CLUSTER - step) {
    // Last core of last stage
    dump_time(2);
    // Sleep until the DMA is done
    mempool_wfi();
    // Get ready to program the next DMA transfer
    return (uint32_t)log_barrier;
  } else if (val == (uint32_t)(next_step - step)) {
    // Last core of this stage
    __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
    return hard_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
  } else if (val == 0 && log_barrier == &round_barrier[0]) {
    // First core of first barrier in first stage
    dump_time(1);
    // Check that the DMA from the previous iteration is done
    uint32_t cluster_id = mempool_get_core_id()/NUM_CORES_PER_CLUSTER;
    dma_wait(cluster_id);
    // Wake up all cores to get to the next phase of the barrier
    wake_up_cluster(cluster_id);
    mempool_wfi();
    // Sleep until all cores hit the barrier
    mempool_wfi();
  } else {
    // Middle cores, sleep until the DMA is done
    mempool_wfi();
    // Middle cores, sleep until all cores hit the barrier
    mempool_wfi();
  }
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t cluster_id = core_id / NUM_CORES_PER_CLUSTER;
  uint32_t core_cluster_id = core_id % NUM_CORES_PER_CLUSTER;
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  // Allocation
  void* alloc_base = (void*)(cluster_id*L1_SIZE_PER_CLUSTER + NUM_CORES_PER_CLUSTER*STACK_SIZE);
  // Local matrices per cluster
  int32_t* in = (int32_t*)(alloc_base); // Size [M*N]
  alloc_base += M*N*sizeof(int32_t);
  int32_t* out = (int32_t*)(alloc_base); // Size [M*N]
  alloc_base += M*N*sizeof(int32_t);
  // Allocate barriers for each core
  // Align alloc_base to have the barriers aligned in memory
  alloc_base = (void*)((uint32_t)(alloc_base + (NUM_BANKS_PER_CLUSTER*sizeof(void) - 1)) & ~(NUM_BANKS_PER_CLUSTER*sizeof(void) - 1));
  uint32_t *round_barrier = (uint32_t*)(alloc_base); // Size [NUM_CORES_PER_CLUSTER]
  alloc_base += NUM_BANKS_PER_CLUSTER*sizeof(uint32_t);

  // Initial setup
  round_barrier[core_cluster_id*BANKING_FACTOR] = 0;

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
  const int last_round = 8;
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
  if (core_cluster_id == 0) {
    dma_memcpy_blocking(cluster_id, (void *)in, (void *)in_l2, M * N / 2 * sizeof(int32_t));
    // Set `bar` to mimic this core being the first passing the `hard_log_barrier`
    // and programing the next transfer and waking up all other cores afterward.
    bar = (uint32_t)round_barrier;
  } else {
    // Wait for the DMA to be done
    mempool_wfi();
    bar = 0;
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
    // Launch DMA for next iteration
    mempool_start_benchmark();
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking(cluster_id, (void *)in_dma, (void *)in_l2,
                               M * N / 2 * sizeof(int32_t));
      }
      if (round != 0) {
        dma_memcpy_nonblocking(cluster_id, (void *)out_l2, (void *)out_dma,
                               M * N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      // Wake up all cores waiting at the hard barrier
      wake_up_cluster(cluster_id);
      mempool_wfi();
      dump_time(0);
    }
    mempool_start_benchmark();
    conv2d_3x3_crazy_parallel((const int32_t *)in_comp, N, M / 2,
                              (const int32_t *)kernel, (int32_t *)out_comp,
                              core_cluster_id, NUM_CORES_PER_CLUSTER);
    mempool_start_benchmark();
    // Barrier
    bar = hard_log_barrier(round_barrier, 1, log2_radix, core_cluster_id);
  }

  // Last write back
  mempool_start_benchmark();
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking(cluster_id, (void *)out_l2, (void *)out_dma,
                        M * N / 2 * sizeof(int32_t));
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    // Wake up all cores waiting at the hard barrier
    wake_up_cluster(cluster_id);
    mempool_wfi();
  }

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  return 0;
}
