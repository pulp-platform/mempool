// Copyright 2024 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Bowen Wang <bowwang@student.ethz.ch>
// Desc:   GEMM f32 benchmark using DAS (Dynamic Address Scrambling)

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_das_gemm_f32.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_matmul_f32.h"

#define NUM_TILES (NUM_CORES / NUM_CORES_PER_TILE)

// Tiles per DAS partition: NUM_TILES = fully interleaved (baseline)
#ifndef TILES_PER_PARTITION
#define TILES_PER_PARTITION NUM_TILES
#endif

// Shared pointers for DAS-allocated matrices
float *volatile shared_a __attribute__((section(".l1")));
float *volatile shared_b __attribute__((section(".l1")));
float *volatile shared_c __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_init(core_id);
  mempool_barrier_init(core_id);

  uint32_t a_size = matrix_M * matrix_N * sizeof(float);
  uint32_t b_size = matrix_N * matrix_P * sizeof(float);
  uint32_t c_size = matrix_M * matrix_P * sizeof(float);

  if (core_id == 0) {
    // Initialize DAS dynamic heap allocator
    mempool_dynamic_heap_alloc_init(core_id);
    alloc_t *das_alloc = get_dynamic_heap_alloc();

    // Allocate matrices in DAS region
    shared_a = (float *)partition_malloc(das_alloc, a_size);
    shared_b = (float *)partition_malloc(das_alloc, b_size);
    shared_c = (float *)partition_malloc(das_alloc, c_size);

    // Configure DAS partitions
    das_config(0, TILES_PER_PARTITION, (uint32_t)shared_a, a_size);
    das_config(1, TILES_PER_PARTITION, (uint32_t)shared_b, b_size);
    das_config(2, TILES_PER_PARTITION, (uint32_t)shared_c, c_size);

    // DMA: copy input matrices from L2 to DAS-allocated L1
    dma_memcpy_blocking(shared_a, l2_A, a_size);
    dma_memcpy_blocking(shared_b, l2_B, b_size);
  }
  mempool_barrier(num_cores);

  // All cores read the shared pointers
  float *matrix_a = shared_a;
  float *matrix_b = shared_b;
  float *matrix_c = shared_c;

  // Benchmark: parallel GEMM
  mempool_start_benchmark();
  matmul_2x2_parallel_f32(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                          matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // Verify against golden result
  mempool_check_f32(matrix_c, l2_C, matrix_M * matrix_P, 0.01f, 0);
  mempool_barrier(num_cores);

  // Cleanup
  if (core_id == 0) {
    alloc_t *das_alloc = get_dynamic_heap_alloc();
    partition_free(das_alloc, shared_c);
    partition_free(das_alloc, shared_b);
    partition_free(das_alloc, shared_a);
  }

  return 0;
}
