// Copyright 2024 ETH Zurich and University of Bologna.
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

// Author: Domenic Wüthrich
//         Diyou Shen     <dishen@student.ethz.ch>

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "data/data_axpy.h"

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"


uint32_t timer = (uint32_t)-1;

// 32-bit AXPY: y = a * x + y
void faxpy_v32b(const float a, const float *x, const float *y, uint32_t round, uint32_t dim) {
  const float *std = y;
  for (uint32_t rnd = 0; rnd < round; rnd ++) {
    std = y;
    // Load vectors
    asm volatile("vle32.v v0, (%0)" ::"r"(x));
    asm volatile("vle32.v v8, (%0)" ::"r"(y));
    x += dim;
    y += dim;

    // Multiply-accumulate
    asm volatile("vfmacc.vf v8, %0, v0" ::"f"(a));

    // Store results
    asm volatile("vse32.v v8, (%0)" ::"r"(std));
  }
}

// 32-bit AXPY: y = a * x + y
void faxpy_v32b_unroll2(const float a, const float *x, const float *y, uint32_t round, uint32_t dim) {
  const float *std1 = y;
  const float *std2 = y;
  for (uint32_t rnd = 0; rnd < round; rnd ++) {
    std1 = y;
    asm volatile("vle32.v v0, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v8, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v8, %0, v0" ::"f"(a));

    std2 = y;
    asm volatile("vle32.v v16, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v24, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v24, %0, v16" ::"f"(a));

    // Store results
    asm volatile("vse32.v v8,  (%0)" ::"r"(std1));
    asm volatile("vse32.v v24, (%0)" ::"r"(std2));
  }
}

// 32-bit AXPY: y = a * x + y
void faxpy_v32b_unroll4(const float a, const float *x, const float *y, uint32_t round, uint32_t dim) {
  const float *std1 = y;
  const float *std2 = y;
  const float *std3 = y;
  const float *std4 = y;

  for (uint32_t rnd = 0; rnd < round; rnd ++) {
    std1 = y;
    asm volatile("vle32.v v0, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v4, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v4, %0, v0" ::"f"(a));

    std2 = y;
    asm volatile("vle32.v v8, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v12, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v12, %0, v8" ::"f"(a));

    std3 = y;
    asm volatile("vle32.v v16, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v20, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v20, %0, v16" ::"f"(a));

    std4 = y;
    asm volatile("vle32.v v24, (%0)" ::"r"(x));
    x += dim;
    asm volatile("vle32.v v28, (%0)" ::"r"(y));
    y += dim;
    asm volatile("vfmacc.vf v28, %0, v24" ::"f"(a));

    // Store results
    asm volatile("vse32.v v4,  (%0)" ::"r"(std1));
    asm volatile("vse32.v v12, (%0)" ::"r"(std2));
    asm volatile("vse32.v v20, (%0)" ::"r"(std3));
    asm volatile("vse32.v v28, (%0)" ::"r"(std4));
  }
}

// Verify the matrices
int verify_matrix(float *matrix, const float *golden, const unsigned int size) {
  int error = 0;
  for (unsigned int j = 0; j < size; ++j) {
    float diff = matrix[j] - golden[j];
    if (diff < 0)
      diff = -diff;
    if (diff > 0.01f)
      error ++;
  }
  return error;
}

int main() {
  const uint32_t num_cores = mempool_get_core_count();
  const uint32_t cid = mempool_get_core_id();
  const uint32_t is_core_active = cid < active_cores;
  const uint32_t dim = axpy_l.M;

  // calculate the number of rounds we need
  // the optimal settings for lmul is 1 for this kernel: full local visits
  const uint32_t lmul = 1;
  const uint32_t vlen_elem = VLEN / 32;
  const uint32_t max_vl = vlen_elem * lmul;

  const uint32_t dim_per_round = max_vl * active_cores;
  const uint32_t round = (dim > dim_per_round) ? dim/dim_per_round : 1;

  const int CHECK = 1;

  if (cid == 0) {
    printf("lmul:%u, dim:%u, rnd:%u\n", lmul, dim_per_round, round);
  }

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  uint32_t timer_start, timer_end;

  // Block dimension of core
  const uint32_t dim_core = (round == 0) ? (dim / active_cores) : max_vl;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Initialize matrices
  if (cid == 0) {
    dma_memcpy_blocking(x, axpy_X_dram,  dim * sizeof(float));
    dma_memcpy_blocking(y, axpy_Y_dram,  dim * sizeof(float));
    dma_memcpy_blocking(r, axpy_GR_dram, dim * sizeof(float));

    printf("finish copy\n");
  }

  alpha[cid] = axpy_alpha_dram;

  float *x_int = x + dim_core * cid;
  float *y_int = y + dim_core * cid;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  uint32_t vl;

  if (is_core_active) {
    if ((lmul == 1) && (lmul < 8))
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
    if (cid == 0)
      timer_start = mempool_get_timer();

    if ((round >= 4) && (lmul < 8))
      faxpy_v32b_unroll4(alpha[cid], x_int, y_int, round >> 2, dim_per_round);
    else if (round >= 2)
      faxpy_v32b_unroll2(alpha[cid], x_int, y_int, round >> 1, dim_per_round);
    else
      faxpy_v32b(alpha[cid], x_int, y_int, round, dim_per_round);
  }

  mempool_barrier(num_cores);

  if (cid == 0) {
    timer_end = mempool_get_timer();
    timer = (timer_end - timer_start);
  }

  // End dump
  if (cid < active_cores)
    mempool_stop_benchmark();

  // Check and display results
  if (cid == 0) {
    unsigned int performance = 1000 * 2 * dim / timer;
    unsigned int utilization = performance / (2 * active_cores * N_FU);

    printf("\n----- (%u) axpy -----\n", dim);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  if (CHECK) {
    if (cid < active_cores) {
      float *y_check = y;
      float *r_check = r;
      uint32_t core_offset = dim / active_cores;

      y_check += (cid*core_offset);
      r_check += (cid*core_offset);

      error[cid] = verify_matrix(y_check, r_check, core_offset);
    }

    mempool_barrier(num_cores);

    if (cid == 0) {
      for (uint32_t i = 1; i < active_cores; i ++) {
        error[0] += error[i];
      }
      printf("Errors: %u\n", error[0]);
    }
  }

  // Wait for core 0 to display the results
  mempool_barrier(num_cores);

  return 0;
}
