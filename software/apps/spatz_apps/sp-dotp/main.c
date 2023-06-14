// Copyright 2022 ETH Zurich and University of Bologna.
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

// Author: Diyou Shen     <dishen@student.ethz.ch>
//         Matteo Perotti <mperotti@iis.ee.ethz.ch>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "data/data_4096_2.h"
// #include "data/data_4096_16.h"
// #include "data/data_8192_2.h"
// #include "data/data_8192_16.h"
// #include "data/data_8192_32.h"
// #include "data/data_16384_64.h"
// #include "kernel/fdotp.c"

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"

#define PARTIAL_TIMER

uint32_t timer = (unsigned int)-1;
// 32-bit dot-product: a * b
float fdotp_v32b(const float *a, const float *b, unsigned int avl, const uint32_t cid) {
  const unsigned int orig_avl = avl;
  unsigned int vl;

  float red;

  #ifdef PARTIAL_TIMER
  uint32_t timer_start, timer_end;
  if (cid == 0) {
    timer_start = mempool_get_timer();
  }
  #endif

  // Stripmine and accumulate a partial reduced vector
  do {
    // Set the vl
    asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));

    // Load chunk a and b
    asm volatile("vle32.v v8,  (%0)" ::"r"(a));
    asm volatile("vle32.v v16, (%0)" ::"r"(b));
    a += vl;
    b += vl;
    // Multiply and accumulate
    if (avl == orig_avl) {
      asm volatile("vfmul.vv v24, v8, v16");
    } else {
      asm volatile("vfmacc.vv v24, v8, v16");
    }
    avl -= vl;
    // asm volatile("vle32.v v8,  (%0)" ::"r"(a));
    // asm volatile("vle32.v v16, (%0)" ::"r"(b));
    // asm volatile("vfmacc.vv v24, v8, v16");

    // // Bump pointers
    // a += vl;
    // b += vl;
    // avl -= vl;
    // mempool_wait(1000);
  } while (avl > 0);

  #ifdef PARTIAL_TIMER
  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = timer_end - timer_start;
  }
  #endif

  // Reduce and return
  asm volatile("vfredusum.vs v0, v24, v0");
  asm volatile("vfmv.f.s %0, v0" : "=f"(red));
  return red;
}

static inline int fp_check(const float a, const float b) {
  const float threshold = 0.01f;

  // Absolute value
  float comp = a - b;
  if (comp < 0)
    comp = -comp;

  return comp > threshold;
}

int main() {
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cid = mempool_get_core_id();
  const unsigned int is_core_active = cid < active_cores;
  const unsigned int dim = dotp_l.M;

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  #ifndef PARTIAL_TIMER
  uint32_t timer_start, timer_end;
  #endif

  // Block dimension of core
  const unsigned int dim_core = dim / active_cores;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Initialize matrices
  if (cid == 0) {
    // init_matrix(a, dotp_A_dram, dim);
    // init_matrix(b, dotp_B_dram, dim);
    dma_memcpy_blocking(a, dotp_A_dram, dim * sizeof(float));
    dma_memcpy_blocking(b, dotp_B_dram, dim * sizeof(float));
    for (uint32_t i = 0; i < active_cores; i ++) {
      result[i] = 0;
    }
    printf("finish copy\n");
  }

  float *a_int = a + dim_core * cid;
  float *b_int = b + dim_core * cid;
  float *final_store = result + active_cores;
  float acc = 0;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Calculate dotp
  if (is_core_active) {
    // Start dump
    mempool_start_benchmark();
    #ifndef PARTIAL_TIMER
    // Start timer
    if (cid == 0)
      timer_start = mempool_get_timer();
    #endif
    // Calculate the result
    acc = fdotp_v32b(a_int, b_int, dim_core, cid);
    result[cid] = acc;
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid == 0) {
    for (unsigned int i = 1; i < active_cores; ++i)
      acc += result[i];
    *final_store = acc;
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // // End timer
  #ifndef PARTIAL_TIMER
  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = timer_end - timer_start;
  }
  #endif
  // End dump
  if (cid < active_cores)
    mempool_stop_benchmark();

  // Check and display results
  if (cid == 0) {
    unsigned int performance = 1000 * 2 * dim / timer;
    unsigned int utilization = performance / (2 * active_cores * N_FPU);

    printf("\n----- (%dx%d) sp fdotp -----\n", dim, dim);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (cid == 0) {
    uint32_t *gold = (uint32_t *) &dotp_result;
    printf("gold:%x\n", (uint32_t) *gold);
    float *output = result + active_cores;
    uint32_t *calc = (uint32_t *) output;
    printf("calc:%x\n", (uint32_t) *calc);
    if (fp_check(dotp_result, *output)) {
      printf("Mismatch!\n");
      return 1;
    }
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
