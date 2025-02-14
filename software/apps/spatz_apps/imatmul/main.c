// Copyright 2021 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Domenic Wüthrich, ETH Zurich

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "data/data_gemm.h"
#include "kernel/sp-imatmul.c"
#include "printf.h"
#ifdef MEMPOOL
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"
#include "encoding.h"
#endif

#define USE_DMA

#ifdef USE_DMA
#include "dma.h"
#endif


// Initialize the matrices
void init_matrix(uint32_t *matrix, const uint32_t *src,
                 const unsigned int rows_start, const unsigned int rows_end,
                 const unsigned int num_columns) {
  for (unsigned int i = rows_start; i < rows_end; ++i) {
    for (unsigned int j = 0; j < num_columns; ++j) {
      matrix[i * num_columns + j] = src[i * num_columns + j];
    }
  }
}

// Verify the matrices
int verify_matrix(int32_t *matrix, const int32_t *checksum,
                  const unsigned int num_rows, const unsigned int num_columns) {
  for (unsigned int i = 0; i < num_rows; ++i) {
    int32_t sum = 0;
    for (unsigned int j = 0; j < num_columns; ++j) {
      sum += (int32_t)matrix[i * num_columns + j];
    }

    if (sum != checksum[i]) {
      printf("W:%d\n", i);
      // return i == 0 ? -1 : (int)i;
    }
  }
  return 0;
}

void print_matrix(int32_t const *matrix, unsigned int num_rows,
                  unsigned int num_columns) {
  printf("0x%8X\n", (unsigned int)matrix);
  for (unsigned int i = 0; i < num_rows; ++i) {
    for (unsigned int j = 0; j < num_columns; ++j) {
      printf("%5u ", (unsigned int)matrix[i * num_columns + j]);
    }
    printf("\n");
  }
}

int main() {
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cores_per_group = num_cores / NUM_GROUPS;
  const unsigned int cid = mempool_get_core_id();
  const unsigned int core_gid = cid % cores_per_group;
  const unsigned int gid = cid / cores_per_group;

  const unsigned int active_groups = NUM_GROUPS;
  const unsigned int active_cores = cores_per_group * active_groups;
  const unsigned int is_core_active = cid < active_cores;

  const unsigned int measure_iterations = 1;

  unsigned int timer_start, timer_end, timer;

  unsigned int m_start, m_end;
  unsigned int p_start, p_end;
  unsigned int kernel_size;

  // Initialize MemPool
  mempool_init(cid);

  // Initialize multicore barrier
  mempool_barrier_init(cid);


  #ifdef USE_DMA
  if (cid == 0) {
    dma_memcpy_blocking(a, gemm_A_dram, (gemm_l.M * gemm_l.K) * sizeof(float));
    dma_memcpy_blocking(b, gemm_B_dram, (gemm_l.K * gemm_l.N) * sizeof(float));
    dma_memcpy_blocking(c, gemm_C_dram, (gemm_l.M * gemm_l.N) * sizeof(float));
    // dma_memcpy_blocking(r, gemm_checksum, gemm_l.M * sizeof(float));

    init_matrix(r, gemm_checksum, 0, 1, gemm_l.M);
  }
  #else
  // Initialize matrices
  init_matrix(a, gemm_A_dram, cid * (gemm_l.M / active_cores),
              (cid + 1) * (gemm_l.M / active_cores), gemm_l.K);
  init_matrix(b, gemm_B_dram, cid * (gemm_l.K / active_cores),
              (cid + 1) * (gemm_l.K / active_cores), gemm_l.N);
  init_matrix(c, gemm_C_dram, cid * (gemm_l.M / active_cores),
              (cid + 1) * (gemm_l.M / active_cores), gemm_l.N);
  // Initialize the checksum
  if (cid == 0) {
    init_matrix(r, gemm_checksum, 0, 1, gemm_l.M);
  }
  #endif

  if (cid == 0)
    printf("finish copy\n");

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Reset timer
  timer = (unsigned int)-1;

  // Set matrix dimension
  kernel_size = 4;

  // Block dimension of group
  const unsigned int dim_group = gemm_l.M / active_groups;
  // Number of parallel cores in m direction
  const unsigned int split_m_count = dim_group / kernel_size;

  if (split_m_count < cores_per_group) {
    // Split P dimension up
    const unsigned int split_p_count = cores_per_group / split_m_count;
    p_start = gemm_l.N / split_p_count * (core_gid % split_p_count);
    p_end = gemm_l.N / split_p_count * ((core_gid % split_p_count) + 1);
    m_start = dim_group * gid + kernel_size * (core_gid / split_p_count);
    m_end = dim_group * gid + kernel_size * (core_gid / split_p_count + 1);
  } else {
    // Work over complete P dimension
    p_start = 0;
    p_end = gemm_l.N;
    m_start = dim_group * gid + (dim_group / cores_per_group) * core_gid;
    m_end = dim_group * gid + (dim_group / cores_per_group) * (core_gid + 1);
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  for (unsigned int i = 0; i < measure_iterations; ++i) {
    // Calculate matmul
    if (is_core_active) {
      // Start timer
      timer_start = mempool_get_timer();

      // Start dump
      // if (cid == 0)
        // start_kernel();

      if (kernel_size == 2) {
        matmul_2xVL((int32_t *)c, (const int32_t *)a, (const int32_t *)b,
                    m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
      } else if (kernel_size == 4) {
        matmul_4xVL((int32_t *)c, (const int32_t *)a, (const int32_t *)b,
                    m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
      } else if (kernel_size == 8) {
        matmul_8xVL((int32_t *)c, (const int32_t *)a, (const int32_t *)b,
                    m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
      } else {
        return -2;
      }
    }

    // Wait for all cores to finish matmul
    mempool_barrier(num_cores);

    // // End dump
    // if (cid == 0)
    //   stop_kernel();

    // End timer and check if new best runtime
    timer_end = mempool_get_timer();
    unsigned int timer_temp = timer_end - timer_start;
    if (cid == 0) {
      if (timer_temp < timer) {
        timer = timer_temp;
      }
    }
  }

  // Check and display results
  if (cid == 0) {
    unsigned int performance =
        1000 * 2 * gemm_l.M * gemm_l.N * gemm_l.K / timer;
    unsigned int utilization = performance / (2 * active_cores * N_IPU);

    printf("\n----- (%dx%d) sp imatmul -----\n", gemm_l.M, gemm_l.N);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (cid == 0) {
    int error =
        verify_matrix((int32_t *)c, (const int32_t *)r, gemm_l.M, gemm_l.N);

    if (error != 0) {
      printf("Error core %d: c[%d]=%u, expected %u\n", cid, error,
             c[error == -1 ? 0 : error], r[error == -1 ? 0 : error]);
      return error;
    }
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
