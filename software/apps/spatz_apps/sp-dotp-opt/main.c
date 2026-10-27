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

// Description
// this kernel is the fully optmized version of dot product.
// Each vector core will only work on the data from local tile

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

#define PARTIAL_TIMER

uint32_t timer = (uint32_t) -1;
// 32-bit dot-product: a * b
void fdotp_v32b_opt_p1(const float *a, const float *b, uint32_t avl, const uint32_t loops, const uint32_t offset) {
  const uint32_t orig_avl = avl;
  uint32_t vl;

  const float *a_in_loop = a;
  const float *a_out_loop = a;
  const float *b_in_loop = b;
  const float *b_out_loop = b;

  for (uint32_t i = 0; i < loops; i ++) {
    // Stripmine and accumulate a partial reduced vector
    do {
      // Set the vl
      asm volatile("vsetvli %0, %1, e32, m1, ta, ma" : "=r"(vl) : "r"(avl));

      // Load chunk a and b
      asm volatile("vle32.v v8,  (%0)" ::"r"(a_in_loop));
      asm volatile("vle32.v v16, (%0)" ::"r"(b_in_loop));
      a_in_loop += vl;
      a_in_loop += vl;
      // Multiply and accumulate
      if (i == 0 & avl == orig_avl) {
        // first loop first calc, do mul
        asm volatile("vfmul.vv v24, v8, v16");
      } else {
        asm volatile("vfmacc.vv v24, v8, v16");
      }
      avl -= vl;
    } while (avl > 0);

    if (i != loops-1) {
      a_out_loop += offset;
      b_out_loop += offset;
      a_in_loop = a_out_loop;
      b_in_loop = b_out_loop;
      avl   =  orig_avl;
    }
  }
}

float fdotp_v32b_opt_p2() {
  float red;
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
  const uint32_t num_cores = mempool_get_core_count();
  const uint32_t cid = mempool_get_core_id();
  const uint32_t dim = dotp_l.M;

  // This represent the element offset of two lines of address inside one tile
  const uint32_t AddrOffset = mempool_get_tile_count() * NUM_BANKS_PER_TILE;

  uint32_t linesize;
  uint32_t active_cores;

  if (dim < AddrOffset) {
    // We cannot use all cores in this case
    active_cores = (dim / NUM_BANKS_PER_TILE) * NUM_CORES_PER_TILE;
    linesize     = dim;
  } else {
    active_cores = num_cores;
    linesize     = AddrOffset;
  }

  const uint32_t is_core_active = cid < active_cores;

  // This is how long one vector can be
  const uint32_t v_len = linesize / active_cores;


  // How many loops one core needs to take
  const uint32_t loops = dim / linesize;

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  uint32_t timer_start, timer_end;
  timer_start = 0;
  timer_end   = 0;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Initialize matrices
  if (cid == 0) {
    dma_memcpy_blocking(a, dotp_A_dram, dim * sizeof(float));
    dma_memcpy_blocking(b, dotp_B_dram, dim * sizeof(float));
    for (uint32_t i = 0; i < active_cores; i ++) {
      result[i] = 0;
    }
    printf("finish copy\n");
  }

  float *a_init = a + cid * v_len;
  float *b_init = b + cid * v_len;
  float *final_store = result + active_cores;
  float acc = 0;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Calculate dotp
  if (is_core_active) {
    // Start timer
    if (cid == 0) {
      mempool_start_benchmark();
      timer_start = mempool_get_timer();
    }

    // Calculate the result
    fdotp_v32b_opt_p1(a_init, b_init, v_len, loops, linesize);
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  #ifdef PARTIAL_TIMER
  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = timer_end - timer_start;
    mempool_stop_benchmark();
  }

  #endif

  if (is_core_active) {
    acc = fdotp_v32b_opt_p2();
    result[cid] = acc;
  }
  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid == 0) {
    for (uint32_t i = 1; i < active_cores; ++i)
      acc += result[i];
    *final_store = acc;
  }

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  #ifndef PARTIAL_TIMER
  // End timer
  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = timer_end - timer_start;
  }
  // End dump
  if (is_core_active)
    mempool_stop_benchmark();
  #endif

  // Check and display results
  if (cid == 0) {
    uint32_t performance = 1000 * 2 * dim / timer;
    uint32_t utilization = performance / (2 * active_cores * N_FPU);

    printf("\n----- (%dx%d) sp fdotp -----\n", dim, dim);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (cid == 0) {
    uint32_t *gold = (uint32_t *) &dotp_result;
    printf("gold:%x\n", (uint32_t) *gold);
    // float *output = result;
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
