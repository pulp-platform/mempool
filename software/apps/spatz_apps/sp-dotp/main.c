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

#include "data/data_dotp.h"

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"


uint32_t timer = (uint32_t)-1;
// 32-bit dot-product: a * b
void fdotp_v32b_p1(const float *a, const float *b, uint32_t round, uint32_t dim) {
  for (uint32_t rnd = 0; rnd < round; rnd ++) {
    // Load chunk a and b
    asm volatile("vle32.v v8,  (%0)" ::"r"(a));
    a += dim;
    asm volatile("vle32.v v16, (%0)" ::"r"(b));
    b += dim;
    if (rnd == 0)
      asm volatile("vfmul.vv v24, v8, v16");
    else
      asm volatile("vfmacc.vv v24, v8, v16");
  }
}

float fdotp_v32b_p2(){
  // Reduce and return
  float red;
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
  const uint32_t num_cores = mempool_get_core_count();
  const uint32_t cid = mempool_get_core_id();
  const uint32_t is_core_active = cid < active_cores;
  const uint32_t dim = dotp_l.M;

  // calculate the number of rounds we need
  // the optimal settings for lmul is 4 for MemPool, 2 for TeraPool
  const uint32_t lmul = 4;
  const uint32_t vlen_elem = VLEN / 32;
  const uint32_t max_vl = vlen_elem * lmul;

  const uint32_t dim_per_round = max_vl * active_cores;
  const uint32_t round = (dim > dim_per_round) ? dim/dim_per_round : 1;

  if (cid == 0) {
    printf("lmul:%u, dim:%u, rnd:%u\n", lmul, dim_per_round, round);
  }

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  uint32_t timer_start, timer_end;

  // Block dimension of core
  const uint32_t dim_core = (round == 0) ? dim / active_cores : max_vl;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Initialize matrices
  if (cid == 0) {
    dma_memcpy_blocking(a, dotp_A_dram, dim * sizeof(float));
    dma_memcpy_blocking(b, dotp_B_dram, dim * sizeof(float));
    for (uint32_t i = 0; i <= active_cores; i ++) {
      result[i] = 0;
    }
    printf("finish copy\n");
  }

  float *a_int = a + dim_core * cid;
  float *b_int = b + dim_core * cid;
  float *final_store = result + active_cores;
  float acc = 0;
  uint32_t vl;

  if (is_core_active) {
    if (lmul == 1)
      asm volatile("vsetvli %0, %1, e32, m1, ta, ma" : "=r"(vl) : "r"(dim_core));
    else if (lmul == 2)
      asm volatile("vsetvli %0, %1, e32, m2, ta, ma" : "=r"(vl) : "r"(dim_core));
    else if (lmul == 4)
      asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(dim_core));
    else if (lmul == 8)
      asm volatile("vsetvli %0, %1, e32, m8, ta, ma" : "=r"(vl) : "r"(dim_core));
    else {
      printf("invalid LMUL settings\n");
      return 1;
    }
    mempool_start_benchmark();
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (is_core_active) {
    if (cid == 0)
      timer_start = mempool_get_timer();

    fdotp_v32b_p1(a_int, b_int, round, dim_per_round);
  }

  mempool_barrier(num_cores);
  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = (timer_end - timer_start);
  }

  if (is_core_active) {
    acc = fdotp_v32b_p2();
    result[cid] = acc;
  }

  if (cid == 0) {
    for (uint32_t i = 0; i < active_cores; ++i)
      *final_store += result[i];
  }

  // End dump
  if (cid < active_cores)
    mempool_stop_benchmark();

  // Check and display results
  if (cid == 0) {
    // The timer did not count the reduction time
    uint32_t performance = (1000 * (2 * dim - dim_per_round)) / timer;
    uint32_t utilization = performance / (2 * active_cores * N_FPU);

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
  }

  // Wait for core 0 to display the results
  mempool_barrier(num_cores);

  return 0;
}
