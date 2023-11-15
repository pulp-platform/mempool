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

// Author: Domenic Wüthrich

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "data/data_axpy.h"
#include "printf.h"
#ifdef MEMPOOL
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"
#endif

// dump(result, 1);
const unsigned int csize = 256;
const unsigned int core_count = 16;
const unsigned int esize = csize*core_count;

float x[esize];
float y[esize];
float r[esize];
float alpha;

// 32-bit AXPY: y = a * x + y
void faxpy_v32b(const float a, const float *x, const float *y,
                unsigned int avl) {
  unsigned int vl;

  // Stripmine and accumulate a partial vector
  do {
    // Set the vl
    asm volatile("vsetvli %0, %1, e32, m8, ta, ma" : "=r"(vl) : "r"(avl));

    // Load vectors
    asm volatile("vle32.v v0, (%0)" ::"r"(x));
    asm volatile("vle32.v v8, (%0)" ::"r"(y));

    // Multiply-accumulate
    asm volatile("vfmacc.vf v8, %0, v0" ::"f"(a));

    // Store results
    asm volatile("vse32.v v8, (%0)" ::"r"(y));

    // Bump pointers
    x += vl;
    y += vl;
    avl -= vl;
  } while (avl > 0);
}

// Initialize the matrices
void init_matrix(float *matrix, const float *src,
                 const unsigned int size, unsigned int cid) {
  for (unsigned int j = cid*size; j < (cid+1)*size; ++j)
    matrix[j] = src[j];
}

// Verify the matrices
int verify_matrix(float *matrix, const float *golden,
                  const unsigned int size, unsigned int cid) {
  int error = 0;
  for (unsigned int j = cid*size; j < (cid+1)*size; ++j) {
    float diff = matrix[j] - golden[j];
    if (diff < 0)
      diff = -diff;
    if (diff > 0.001f)
      error ++;
  }
  return error;
}

int main() {
  const unsigned int num_cores = mempool_get_core_count();
  const unsigned int cores_per_group = num_cores / NUM_GROUPS;
  const unsigned int cid = mempool_get_core_id();

  unsigned int timer_start, timer_end, timer;

  // Initialize MemPool
  mempool_init(cid);

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  // Reset timer
  timer = (unsigned int)-1;

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  float *x_, *y_;
  alpha = axpy_alpha_dram;
  unsigned int remaining_elem;


  if (cid < core_count) {
    init_matrix(x, axpy_X_dram, csize, cid);
    init_matrix(y, axpy_Y_dram, csize, cid);
    init_matrix(r, axpy_GR_dram, csize, cid);
    x_ = x + cid * csize;
    y_ = y + cid * csize;
  }

  if (cid == 0)
    printf("start calc\n");

  mempool_barrier(num_cores);

  if (cid < core_count) {
    timer_start = mempool_get_timer();
    faxpy_v32b(alpha, x_, y_, csize);
  }

  // Wait for all cores to finish matmul
  mempool_barrier(num_cores);

  // End timer and check if new best runtime
  timer_end = mempool_get_timer();
  if (cid == 0) {
    unsigned int timer_temp = timer_end - timer_start;
    if (timer_temp < timer) {
      timer = timer_temp;
    }
  }

  // Check and display results
  if (cid == 0) {
    unsigned int performance = 1000 * 2 * 16 / timer;
    unsigned int utilization = performance / (2 * core_count * N_FPU);

    printf("\n----- (%u) axpy -----\n", esize);
    printf("The execution took %u cycles.\n", timer);
    printf("The performance is %u OP/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  mempool_barrier(num_cores);
  if (cid == 0)
    printf("start check\n");

  if (cid == 0) {
    int error = verify_matrix(y, r, esize, cid);
    printf("Errors: %d\n", error);
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return error;
}
