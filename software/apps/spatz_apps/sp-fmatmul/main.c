// Copyright 2023 ETH Zurich and University of Bologna.
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

// Author: Matheus Cavalcante, ETH Zurich


#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "printf.h"
#ifdef MEMPOOL
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"
#endif
// #include "data/data_64_64_64.h"
// #include "data/data_128_128_128.h"
// #include "data/data_128_256_128.h"
// #include "data/data_4096_32_64.h"
#include "data/data_1024_32_64.h"
// #include "data/data_512_32_64.h"
// #include "data/data_256_32_64.h"
// #include "data/data_256_256_256.h"
#include "kernel/sp-fmatmul.c"

// set the number of cores used to calculate
const unsigned int active_core = 128;

// Initialize the matrices
void init_matrix(float *matrix, const float *src,
                 const unsigned int size, const unsigned int cid) {
  for (unsigned int j = cid*size; j < (cid+1)*size; ++j)
    matrix[j] = src[j];
}

// Verify the matrices
int verify_matrix(float *matrix, const float *checksum,
                  const unsigned int num_rows, const unsigned int num_columns) {
  int error = 0;
  for (unsigned int i = 0; i < num_rows; ++i) {
    float sum = 0;
    for (unsigned int j = 0; j < num_columns; ++j) {
      sum += (float)matrix[i * num_columns + j];
    }

    float diff = sum - (float)checksum[i];
    if (diff < 0)
      diff = -diff;
    if (diff > 0.001f) {
      return i == 0 ? -1 : (int)i;
    }
  }
  return error;
}

int main() {
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cid = mempool_get_core_id();

  const unsigned int measure_iterations = 1;

  unsigned int timer_start, timer_end, timer;

  unsigned int m_start, m_end;
  unsigned int p_start, p_end;
  unsigned int kernel_size;

  mempool_init(cid);
  mempool_barrier_init(cid);

  // Reset timer
  timer = (unsigned int)-1;

  // Set matrix dimension
  kernel_size = 4;

  // Work over complete P dimension
  p_start = 0;
  p_end = gemm_l.N;
  m_start = (gemm_l.M / active_core) * cid;
  m_end = (gemm_l.M / active_core) * (cid + 1);

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid < active_core) {
    if (cid == 0)
      printf("init a\n");
    init_matrix(a, gemm_A_dram,   (gemm_l.M * gemm_l.K)/active_core, cid);
    if (cid == 0)
      printf("init b\n");
    init_matrix(b, gemm_B_dram,   (gemm_l.K * gemm_l.N)/active_core, cid);
    if (cid == 0)
      printf("init c\n");
    init_matrix(c, gemm_C_dram,   (gemm_l.M * gemm_l.N)/active_core, cid);
    if (cid == 0)
      printf("init r\n");
    init_matrix(r, gemm_checksum, (gemm_l.M)/active_core, cid);
  }

  if (cid == 0) {
    printf("finish\n");
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid == 0) {
    printf("start calc\n");
  }

  // Calculate matmul
  for (unsigned int i = 0; i < measure_iterations; ++i) {
    timer_start = mempool_get_timer();

    if (cid < active_core) {
      if (kernel_size == 2) {
        mempool_start_benchmark();
        matmul_2xVL(c, a, b, m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
        mempool_stop_benchmark();
      } else if (kernel_size == 4) {
        mempool_start_benchmark();
        matmul_4xVL(c, a, b, m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
        mempool_stop_benchmark();
      } else if (kernel_size == 8) {
        mempool_start_benchmark();
        matmul_8xVL(c, a, b, m_start, m_end, gemm_l.K, gemm_l.N, p_start, p_end);
        mempool_stop_benchmark();
      } else {
        return -2;
      }
    }
    // Wait for all cores to finish
    mempool_barrier(num_cores);

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
    long unsigned int performance =
        1000 * 2 * gemm_l.M * gemm_l.N * gemm_l.K / timer;
    long unsigned int utilization = performance / (2 * active_core * N_FPU);

    printf("\n----- (%dx%d) sp fmatmul -----\n", gemm_l.M, gemm_l.N);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %ld OP/1000cycle (%ld%%o utilization).\n",
           performance, utilization);
  }

  if (cid == 0) {
    int error =
        verify_matrix(c, (const float *)gemm_checksum, gemm_l.M, gemm_l.N);

    if (error != 0) {
      printf("Error core %d: c[%d]=%u\n", cid, error, (int)c[error]);
      return error;
    }
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  return 0;
}
