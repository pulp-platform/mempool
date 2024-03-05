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
#include "kernel/sp-fmatmul.c"
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
void init_matrix(float *matrix, const float *src,
                 const uint32_t rows_start, const uint32_t rows_end,
                 const uint32_t num_columns) {
  for (uint32_t i = rows_start; i < rows_end; ++i) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      matrix[i * num_columns + j] = src[i * num_columns + j];
    }
  }
}

// Verify the matrices
int verify_matrix(float *matrix, const float *checksum,
                  const uint32_t num_rows, const uint32_t num_columns) {
  for (uint32_t i = 0; i < num_rows; ++i) {
    float sum = 0;
    for (uint32_t j = 0; j < num_columns; ++j) {
      sum += (float)matrix[i * num_columns + j];
    }

    float diff = (float)sum - (float)checksum[i];//(float)matrix[i * num_columns + j] - (float)checksum[i * num_columns + j];
    float prec = (float)0.001;
    if (diff < 0)
      diff = -diff;
    if (diff > prec) {
      return (i) == 0 ? -1 : (int)(i);
    }
  // }
  }
  return 0;
}

void print_matrix(float const *matrix, uint32_t num_rows,
                  uint32_t num_columns) {
  printf("0x%8X\n", (uint32_t)matrix);
  for (uint32_t i = 0; i < num_rows; ++i) {
    for (uint32_t j = 0; j < num_columns; ++j) {
      printf("%5u ", (uint32_t)matrix[i * num_columns + j]);
    }
    printf("\n");
  }
}

// Matrix A: MxN
// Matrix B: NxP
// Matrix C: MxP

int main() {
  const uint32_t num_cores = mempool_get_core_count();
  const uint32_t cores_per_group = num_cores / NUM_GROUPS;
  const uint32_t cid = mempool_get_core_id();
  const uint32_t core_gid = cid % cores_per_group;
  const uint32_t gid = cid / cores_per_group;

  const uint32_t active_groups = 4;
  const uint32_t active_cores = cores_per_group * active_groups;
  const uint32_t is_core_active = cid < active_cores;

  const uint32_t measure_iterations = 1;

  uint32_t timer_start, timer_end, timer;

  uint32_t m_start, m_end;
  uint32_t p_start, p_end;
  uint32_t kernel_size;

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  // Reset timer
  timer = (uint32_t)-1;

  // Set matrix dimension
  kernel_size = 8;

  // Block dimension of group
  const uint32_t dim_group = gemm_l.M / active_groups;
  // Number of parallel cores in m direction
  const uint32_t split_m_count = dim_group / kernel_size;

  if (split_m_count < cores_per_group) {
    // Split P dimension up
    const uint32_t split_p_count = cores_per_group / split_m_count;
    p_start = gemm_l.P / split_p_count * (core_gid % split_p_count);
    p_end   = gemm_l.P / split_p_count * ((core_gid % split_p_count) + 1);
    m_start = dim_group * gid + kernel_size * (core_gid / split_p_count);
    m_end   = dim_group * gid + kernel_size * (core_gid / split_p_count + 1);
  } else {
    // Work over complete P dimension
    p_start = 0;
    p_end   = gemm_l.P;
    m_start = dim_group * gid + (dim_group / cores_per_group) * core_gid;
    m_end   = dim_group * gid + (dim_group / cores_per_group) * (core_gid + 1);
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  #ifdef USE_DMA
  if (cid == 0) {
    dma_memcpy_blocking(a, gemm_A_dram, (gemm_l.M * gemm_l.N) * sizeof(float));
    dma_memcpy_blocking(b, gemm_B_dram, (gemm_l.N * gemm_l.P) * sizeof(float));
    dma_memcpy_blocking(c, gemm_C_dram, (gemm_l.N * gemm_l.P) * sizeof(float));
    // dma_memcpy_blocking(r, gemm_checksum, gemm_l.M * sizeof(float));

    init_matrix(r, gemm_checksum, 0, 1, gemm_l.M);
  }
  #else
  // Initialize matrices
  init_matrix(a, gemm_A_dram, cid * (gemm_l.M / active_cores),
              (cid + 1) * (gemm_l.M / active_cores), gemm_l.N);
  init_matrix(b, gemm_B_dram, cid * (gemm_l.N / active_cores),
              (cid + 1) * (gemm_l.N / active_cores), gemm_l.P);
  init_matrix(c, gemm_C_dram, cid * (gemm_l.M / active_cores),
              (cid + 1) * (gemm_l.M / active_cores), gemm_l.P);
  // Initialize the checksum
  if (cid == 0) {
    init_matrix(r, gemm_checksum, 0, 1, gemm_l.M);
  }
  #endif

  if (cid == 0)
    printf("finish copy\n");

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  for (uint32_t i = 0; i < measure_iterations; ++i) {
    // Calculate matmul
    if (is_core_active) {
      // Start timer
      timer_start = mempool_get_timer();

      // Start dump
      if (cid == 0)
        mempool_start_benchmark();

      if (kernel_size == 2) {
        matmul_2xVL(c, a, b, m_start, m_end, gemm_l.N, gemm_l.P, p_start,
                    p_end);
      } else if (kernel_size == 4) {
        matmul_4xVL(c, a, b, m_start, m_end, gemm_l.N, gemm_l.P, p_start,
                    p_end);
      } else if (kernel_size == 8) {
        matmul_8xVL(c, a, b, m_start, m_end, gemm_l.N, gemm_l.P, p_start,
                    p_end);
      } else {
        return -2;
      }
    }

    // Wait for all cores to finish matmul
    mempool_barrier(num_cores);

    // End dump
    if (cid == 0)
      mempool_stop_benchmark();

    // End timer and check if new best runtime
    timer_end = mempool_get_timer();
    uint32_t timer_temp = timer_end - timer_start;
    if (cid == 0) {
      if (timer_temp < timer) {
        timer = timer_temp;
      }
    }
  }

  // Check and display results
  if (cid == 0) {
    long unsigned int performance =
        1000 * 2 * gemm_l.M * gemm_l.P * gemm_l.N / timer;
    long unsigned int utilization = performance / (2 * active_cores * N_FPU);

    printf("\n----- (%dx%d) sp fmatmul -----\n", gemm_l.M, gemm_l.P);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (cid == 0) {
    int error =
        verify_matrix((float *)c, (const float *)r, gemm_l.M, gemm_l.P);
    // int error =
    //     verify_matrix((float *)c, (const float *)gemm_checksum, gemm_l.M, gemm_l.P);

    if (error != 0) {
      printf("Error core %d: c[%d]=%x\n", cid, error, (int)c[error]);
      return error;
    }
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
