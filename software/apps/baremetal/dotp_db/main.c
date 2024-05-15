// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "baremetal/mempool_dotp_i32p.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Max N is NUM_BANKS_PER_CLUSTER * rows that fit L1
#if NUM_CORES_PER_CLUSTER == 16
#define N (64 * 96)
#define LOG_RADIX 2
#elif NUM_CORES_PER_CLUSTER == 32
#define N (128 * 96)
#define LOG_RADIX 5
#elif NUM_CORES_PER_CLUSTER == 64
#define N (256 * 96)
#define LOG_RADIX 3
#elif NUM_CORES_PER_CLUSTER == 128
#define N (512 * 96)
#define LOG_RADIX 7
#elif NUM_CORES_PER_CLUSTER == 256
#define N (1024 * 96)
#define LOG_RADIX 4
#endif

dump(time, 0);

// vec_x_l2_flat from `data.h`
// vec_y_l2_flat from `data.h`
int32_t result __attribute__((section(".l2")));

uint32_t final_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix,
                           uint32_t core_id) {
  uint32_t *log_barrier = &round_barrier[(core_id / step) * step + (step >> log2_radix) - 1];

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  // dump_barrier(step * SEQ_MEM_SIZE*SEQ_MEM_SIZE+(uint32_t)log_barrier + val);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES_PER_CLUSTER) {
      // Last stage
      dump_time(2);
      // Clear wfi that was triggered by the first core
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return final_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
    }
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
  uint32_t *log_barrier = &round_barrier[(core_id / step) * step + (step >> log2_radix) - 1];

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  // dump_barrier(step * SEQ_MEM_SIZE*SEQ_MEM_SIZE+(uint32_t)log_barrier + val);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES_PER_CLUSTER) {
      // Last stage
      dump_time(2);
      // Clear wfi that was triggered by the first core
      mempool_wfi();
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return dma_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
    }
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

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t cluster_id = core_id / NUM_CORES_PER_CLUSTER;
  uint32_t core_cluster_id = core_id % NUM_CORES_PER_CLUSTER;
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  // Allocation
  void* alloc_base = (void*)(cluster_id*L1_SIZE_PER_CLUSTER + NUM_CORES_PER_CLUSTER*STACK_SIZE);
  // Local matrices per cluster
  int32_t* vec_x = (int32_t*)(alloc_base); // Size [matrix_M*matrix_N]
  alloc_base += N*sizeof(int32_t);
  int32_t* vec_y = (int32_t*)(alloc_base); // Size [matrix_M*matrix_N]
  alloc_base += N*sizeof(int32_t);
  int32_t* cluster_result = (int32_t*)(alloc_base); // Size 1
  alloc_base += sizeof(int32_t);
  // Allocate barriers for each core
  uint32_t *round_barrier = (uint32_t*)(alloc_base); // Size [NUM_CORES_PER_CLUSTER]
  alloc_base += NUM_CORES_PER_CLUSTER*sizeof(uint32_t);

  // Initial setup
  round_barrier[core_cluster_id] = 0;

  // Initialize img
  mempool_start_benchmark();
  if (core_cluster_id == 0) {
    result = 0;
    *cluster_result = 0;
    dma_memcpy_nonblocking(cluster_id, (void *)vec_x, (void *)vec_x_l2_flat,
                           N / 2 * sizeof(int32_t));
    dma_memcpy_blocking(cluster_id, (void *)vec_y, (void *)vec_y_l2_flat,
                        N / 2 * sizeof(int32_t));
  }

  // Double-buffered convolution
  const int last_round = 8;
  // const int first = 0;
  const uint32_t log2_radix = LOG_RADIX;
  const uint32_t radix = 1 << log2_radix;

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Initial launch, Core 0 transfered the data in
  if (core_cluster_id == 0) {
    wake_up_cluster(cluster_id);
  }
  const int32_t *vec_x_comp;
  const int32_t *vec_x_dma;
  const int32_t *vec_y_comp;
  const int32_t *vec_y_dma;

  const int32_t *vec_x_in;
  const int32_t *vec_y_in;
  uint32_t bar;

  int32_t sum = 0;

  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      vec_x_comp = (const int32_t *)&vec_x[0];
      vec_x_dma = (const int32_t *)&vec_x[N / 2];
      vec_y_comp = (const int32_t *)&vec_y[0];
      vec_y_dma = (const int32_t *)&vec_y[N / 2];

      vec_x_in = (const int32_t *)&vec_x_l2_flat[N / 2];
      vec_y_in = (const int32_t *)&vec_y_l2_flat[N / 2];
    } else {
      vec_x_comp = (const int32_t *)&vec_x[N / 2];
      vec_x_dma = (const int32_t *)&vec_x[0];
      vec_y_comp = (const int32_t *)&vec_y[N / 2];
      vec_y_dma = (const int32_t *)&vec_y[0];

      vec_x_in = (const int32_t *)&vec_x_l2_flat[0];
      vec_y_in = (const int32_t *)&vec_y_l2_flat[0];
    }
    mempool_wfi();
    // Barrier, launch DMA for next iteration
    bar = dma_log_barrier(round_barrier, radix, log2_radix, core_cluster_id);
    mempool_start_benchmark();
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking(cluster_id, (void *)vec_x_dma, (void *)vec_x_in,
                               N / 2 * sizeof(int32_t));
        dma_memcpy_nonblocking(cluster_id, (void *)vec_y_dma, (void *)vec_y_in,
                               N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      if (round != last_round - 1) {
        wake_up_cluster(cluster_id);
      }
    }
    mempool_start_benchmark();
    sum += dotp_parallel((const int32_t *)vec_x_comp, (int32_t *)vec_y_comp,
                         N / 2, core_cluster_id, NUM_CORES_PER_CLUSTER);
    mempool_start_benchmark();
  }
  __atomic_fetch_add(cluster_result, sum, __ATOMIC_RELAXED);

  // Last write back
  bar = final_log_barrier(round_barrier, radix, log2_radix, core_cluster_id);
  mempool_start_benchmark();
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    __atomic_fetch_add(&result, cluster_result, __ATOMIC_RELAXED);
    // We are the last one, reset the barrier
    __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
    wake_up_cluster(cluster_id);
    mempool_wfi();
  }

  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  return 0;
}
