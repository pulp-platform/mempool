// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "baremetal/mempool_matmul_i32p.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Define Matrix dimensions:
// C = AB with A=[MxN], B=[NxP], C=[MxP]

//// SWEEP SIZES
// #if NUM_CORES_PER_CLUSTER == 16
// #define LOG_RADIX 2
// #elif NUM_CORES_PER_CLUSTER == 32
// #define LOG_RADIX 5
// #elif NUM_CORES_PER_CLUSTER == 64
// #define LOG_RADIX 3
// #elif NUM_CORES_PER_CLUSTER == 128
// #define LOG_RADIX 7
// #elif NUM_CORES_PER_CLUSTER == 256
// #define LOG_RADIX 4
// #endif
// #define matrix_M (MATRIX_SIZE)
// #define matrix_N (MATRIX_SIZE)
// #define matrix_P (MATRIX_SIZE)

//// MAX SIZES
#if NUM_CORES_PER_CLUSTER == 16
#define matrix_M 48
#define matrix_N 48
#define matrix_P 48
#define LOG_RADIX 2
#elif NUM_CORES_PER_CLUSTER == 32
#define matrix_M 64
#define matrix_N 64
#define matrix_P 64
#define LOG_RADIX 5
#elif NUM_CORES_PER_CLUSTER == 64
#define matrix_M 96
#define matrix_N 96
#define matrix_P 96
#define LOG_RADIX 3
#elif NUM_CORES_PER_CLUSTER == 128
#define matrix_M 128
#define matrix_N 128
#define matrix_P 128
#define LOG_RADIX 7
#elif NUM_CORES_PER_CLUSTER == 256
#define matrix_M 192
#define matrix_N 192
#define matrix_P 192
#define LOG_RADIX 4
#endif

dump(time, 0);
dump(debug, 1);

// a_l2_flat from `data.h`
// b_l2_flat from `data.h`
int32_t matrix_out[matrix_M * matrix_P] __attribute__((section(".l2")))
__attribute__((aligned(NUM_CORES * BANKING_FACTOR * 4)));

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
    if (val == 0 && log_barrier == &round_barrier[0])
      dump_time(1);
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

uint32_t hard_log_barrier(uint32_t* round_barrier, uint32_t step, uint32_t log2_radix, uint32_t core_id) {
  uint32_t *log_barrier = &round_barrier[(core_id / step) * step + (step >> log2_radix) - 1];

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES_PER_CLUSTER) {
      // Last stage
      dump_time(2);
      // Sleep until the DMA is done
      mempool_wfi();
      // Get ready to program the next DMA transfer
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return hard_log_barrier(round_barrier, step << log2_radix, log2_radix, core_id);
    }
  } else if (val == 0 && log_barrier == &round_barrier[0]) {
    // First core of first barrier in first stage
    dump_time(1);
    // Check that the DMA from the previous iteration is done
    uint32_t cluster_id = mempool_get_core_id()/NUM_CORES_PER_CLUSTER;
    dma_wait(cluster_id);
    // Wake up all cores to get to the next phase of the barrier
    wake_up_cluster(cluster_id);
    mempool_wfi();
    dump_time(0);
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
  int32_t* matrix_a1 = (int32_t*)(alloc_base); // Size [matrix_M*matrix_N]
  alloc_base += matrix_M*matrix_N*sizeof(int32_t);
  int32_t* matrix_a2 = (int32_t*)(alloc_base); // Size [matrix_M*matrix_N]
  alloc_base += matrix_M*matrix_N*sizeof(int32_t);
  int32_t* matrix_b1 = (int32_t*)(alloc_base); // Size [matrix_N * matrix_P]
  alloc_base += matrix_N*matrix_P*sizeof(int32_t);
  int32_t* matrix_b2 = (int32_t*)(alloc_base); // Size [matrix_N * matrix_P]
  alloc_base += matrix_N*matrix_P*sizeof(int32_t);
  int32_t* matrix_c = (int32_t*)(alloc_base); // Size [matrix_M * matrix_P]
  alloc_base += matrix_M*matrix_P*sizeof(int32_t);
  // Allocate barriers for each core
  // Align alloc_base to have the barriers aligned in memory
  alloc_base = (void*)((uint32_t)(alloc_base + (NUM_BANKS_PER_CLUSTER*sizeof(void) - 1)) & ~(NUM_BANKS_PER_CLUSTER*sizeof(void) - 1));
  uint32_t *round_barrier = (uint32_t*)(alloc_base); // Size [NUM_CORES_PER_CLUSTER]
  alloc_base += NUM_CORES_PER_CLUSTER*sizeof(uint32_t);

  // Initial setup
  round_barrier[core_cluster_id] = 0;

  // Double-buffered convolution
  const int last_round = 8;
  // const int first = 0;
  const uint32_t log2_radix = LOG_RADIX;
  const uint32_t radix = 1 << log2_radix;

  const int32_t *a_comp;
  const int32_t *b_comp;
  const int32_t *a_dma;
  const int32_t *b_dma;
  uint32_t bar;

  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  // Initialize img
  if (core_cluster_id == 0) {
    dma_memcpy_nonblocking(cluster_id, (void *)matrix_a1, (void *)a_l2_flat,
                           matrix_M * matrix_N * sizeof(int32_t));
    dma_memcpy_blocking(cluster_id, (void *)matrix_b1, (void *)b_l2_flat,
                        matrix_N * matrix_P * sizeof(int32_t));
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
    // Launch DMA for next iteration
    mempool_start_benchmark();
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking(cluster_id, (void *)a_dma, (void *)a_l2_flat,
                               matrix_M * matrix_N * sizeof(int32_t));
        dma_memcpy_nonblocking(cluster_id, (void *)b_dma, (void *)b_l2_flat,
                               matrix_N * matrix_P * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t *)bar, 0, __ATOMIC_RELAXED);
      // Wake up all cores waiting at the hard barrier
      wake_up_cluster(cluster_id);
      mempool_wfi();
    }
    mempool_start_benchmark();
    mat_mul_unrolled_4x4_parallel_asm(a_comp, b_comp, matrix_c, matrix_M,
                                      matrix_N, matrix_P, core_cluster_id, NUM_CORES_PER_CLUSTER);
    mempool_start_benchmark();
    // Barrier
    bar = hard_log_barrier(round_barrier, radix, log2_radix, core_cluster_id);
  }

  // Last write back
  mempool_start_benchmark();
  if (bar) {
    // We are the last one, reset the barrier
    // The old data can now be overwritten with a new DMA request
    dma_memcpy_blocking(cluster_id, (void *)matrix_out, (void *)matrix_c,
                        matrix_M * matrix_P * sizeof(int32_t));
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
