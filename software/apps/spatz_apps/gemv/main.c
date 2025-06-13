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

// Author: Diyou Shen,              ETH Zurich <dishen@iis.ee.ethz.ch>
//         Navaneeth Kunhi Purayil, ETH Zurich <nkunhi@iis.ee.ethz.ch>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "data/data_gemv.h"
#include "kernel/gemv.c"
#include "printf.h"
#ifdef MEMPOOL
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"
#include "encoding.h"
#endif

#include "dma.h"

#if (PREC == 32)
#define T float
#elif (PREC == 16)
#define T __fp16
#endif

// #define DEBUG

static inline int fp_check(const T *a, const T *b) {
  const T threshold = 0.001f;

  // Absolute value
  float comp = (float)*a - (float)*b;
  if (comp < 0)
    comp = -comp;

  return comp > threshold;
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
// Vector B: Nx1
// Vector C: Mx1

int main() {
  const uint32_t num_cores          = mempool_get_core_count();
  const uint32_t cid                = mempool_get_core_id();

  const uint32_t measure_iterations = 1;

  const uint32_t is_core_active     = (cid < active_cores);

  // algorithm switch
  const uint32_t unroll_m           = 0;

  uint32_t timer_start, timer_end, timer;

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  const uint32_t size_A = (gemv_l.M * gemv_l.N) * sizeof(float);
  const uint32_t size_B = (gemv_l.N) * sizeof(float);
  const uint32_t size_C = (gemv_l.M) * sizeof(float);

  // Reset timer
  timer = (uint32_t)-1;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid == 0) {
    dma_memcpy_blocking(a,      gemv_A_dram, size_A);
    for (uint32_t i = 0; i < multiB; i ++) {
      // Copy multiple B vector to reduce conflicts
      dma_memcpy_blocking(b[i], gemv_B_dram, size_B);
    }
    dma_memcpy_blocking(result, gemv_result, size_C);
  #ifdef DEBUG
    printf("A:%p,B:%p,C:%p\n", a, b, result);
    printf("A:%x,B:%x,C:%x\n", size_A, size_B, size_C);
  #endif
  }

  if (cid == 0)
    printf("finish copy\n");

  unsigned int m_core = gemv_l.M / active_cores;

  // Calculate internal pointers
  T *a_core      = a + m_core * cid;
  T *b_core      = b[cid * multiB / num_cores];
  T *result_core = result + m_core * cid;

  #ifdef DEBUG
  if (cid == 0)
    printf("m_core:%x\n", m_core);

  for (uint32_t i = 0; i < active_cores; ++i) {
    if (cid == i) {
      printf("Core%u,A:%p,C:%p\n", i, a_core, result_core);
    } else {
      // Add an idle delay here to avoid triggering bugs in barrier
      mempool_wait(100);
    }
    mempool_barrier(num_cores);
  }
  #endif

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

      // gemv_v32b_m4(a_core, b, result_core, gemv_l.M, m_core, gemv_l.N);

      // Calculate gemv
      if (sizeof(T) == 4)
        if (unroll_m)
          gemv_v32b_m4_unroll_M(a_core, b, result_core, gemv_l.M, m_core, gemv_l.N);
        else
          gemv_v32b_m4(a_core, b, result_core, gemv_l.M, m_core, gemv_l.N);
      else if (sizeof(T) == 2)
        gemv_v16b_m4(a_core, b, result_core, gemv_l.M, m_core, gemv_l.N);
      else
        return -2;
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

    long unsigned int performance = 1000 * 2 * gemv_l.M * gemv_l.N / timer;
    long unsigned int utilization =
        performance / (2 * active_cores * N_FPU * (4 / sizeof(T)));

    printf("\n----- (%d x %d) x (%d x 1) gemv -----\n", gemv_l.M, gemv_l.N, gemv_l.N);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (is_core_active) {
    for (uint32_t i = 0; i < m_core; i++) {
      if (fp_check(&result[i+m_core*cid], &gemv_result[i+m_core*cid])) {
        printf("Error: ID: %i Result = %f, Golden = %f\n", i, result[i+m_core*i], gemv_result[i+m_core*i]);
        return -1;
      }
    }
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
