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

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "alloc.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data.h"

// #define DEBUG

uint32_t vle_benchmark_n2(const int *addr, uint32_t avl, const uint32_t cid, const uint32_t num_cores) {
  uint32_t vl;
  uint32_t timer = 0;

  asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));
  mempool_barrier(num_cores);

  if (cid == 0)
    timer = mempool_get_timer();

  asm volatile("vle32.v v0,  (%0)" ::"r"(addr));
  asm volatile("vle32.v v4,  (%0)" ::"r"(addr));

  mempool_barrier(num_cores);

  if (cid == 0)
    timer = mempool_get_timer()- timer;

  return timer;
}

uint32_t vle_benchmark_n4(const int *addr1, const int *addr2, uint32_t avl, const uint32_t cid, const uint32_t num_cores) {
  uint32_t vl;
  uint32_t timer = 0;

  asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(avl));
  mempool_barrier(num_cores);

  if (cid == 0)
    timer = mempool_get_timer();

  asm volatile("vle32.v v0,  (%0)" ::"r"(addr1));
  asm volatile("vle32.v v4,  (%0)" ::"r"(addr1));
  asm volatile("vle32.v v8,  (%0)" ::"r"(addr2));
  asm volatile("vle32.v v12, (%0)" ::"r"(addr2));

  mempool_barrier(num_cores);
  if (cid == 0)
    timer = mempool_get_timer()- timer;

  return timer;
}


uint32_t barrier_test(const uint32_t cid, const uint32_t num_cores) {
  uint32_t timer = 0;
  // mempool_barrier(num_cores);
  if (cid == 0)
    timer = mempool_get_timer();

  mempool_barrier(num_cores);

  if (cid == 0)
    timer = mempool_get_timer()- timer;

  return timer;
}

// Vector A occupies two rows of entire L1
// Each core will tries to load a vector at random location in the first row of A
int main() {
  // vector length grouping factor
  const uint32_t Vec_Lmul = 4;
  // measurement rounds
  const uint32_t measure_iterations = R;
  // element width (8, 16, 32)
  const uint32_t elem_width = 32;
  // vector length per vector (elements)
  const uint32_t Vec_Len  = (VLEN < 512) ? VLEN/elem_width : 512/elem_width;


  const uint32_t num_cores = mempool_get_core_count();
  const uint32_t cid = mempool_get_core_id();
  const uint32_t dim = M;
  // const uint32_t rnd = R;
  const uint32_t v_len = Vec_Lmul * Vec_Len;

  // Initialize multicore barrier
  mempool_barrier_init(cid);

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  // Initialize matrices
  if (cid == 0) {
    dma_memcpy_blocking(data_l1, data_dram, dim * sizeof(int));
    dma_memcpy_blocking(offset_l1, offset_dram, (num_cores * measure_iterations) * sizeof(int));
  #ifdef DEBUG
    printf("finish copy\n");
  #endif
  }

  // // Each cores starting address
  uint32_t *offset_p = offset_l1;
  offset_p += cid;


  // int *addr = data_l1;
  int *addr1 = data_l1;
  int *addr2 = data_l1;
  int *addr3 = data_l1;
  int *addr4 = data_l1;
  uint32_t timer = 0;
  uint32_t timer_tot = 0;

  // // Used to compasate the cycles spent on barrier
  // uint32_t barrier_timer = 0;
  // uint32_t barrier_timer_tot = 0;
  uint32_t vl;
  asm volatile("vsetvli %0, %1, e32, m4, ta, ma" : "=r"(vl) : "r"(v_len));

  // Wait for all cores to finish
  mempool_barrier(num_cores);

  if (cid == 0) {
    mempool_start_benchmark();
    timer = mempool_get_timer();
  }

  for (uint32_t i = 0; i < measure_iterations/4; i ++) {
    addr1 = data_l1 + *offset_p;
    offset_p += num_cores;
    addr2 = data_l1 + *offset_p;
    offset_p += num_cores;
    asm volatile("vle32.v v0,  (%0)" ::"r"(addr1));
    asm volatile("vle32.v v4,  (%0)" ::"r"(addr2));
    addr3 = data_l1 + *offset_p;
    offset_p += num_cores;
    addr4 = data_l1 + *offset_p;
    offset_p += num_cores;
    asm volatile("vle32.v v8,  (%0)" ::"r"(addr3));
    asm volatile("vle32.v v12, (%0)" ::"r"(addr4));
  }

  if (cid == 0) {
    mempool_stop_benchmark();
    timer_tot = mempool_get_timer()- timer;
  }

  // Check and display results
  if (cid == 0) {
    // uint32_t timer_avg = timer_tot * 1000 / measure_iterations;
    // number of load one core will execute for 1000 cycles
    uint32_t performance = measure_iterations * v_len * 1000 / timer_tot;
    // Each cycle one core can load at most N_FU elements
    uint32_t utilization = performance / N_FU;

    printf("\n----- (%dx%d) vle%d -----\n", measure_iterations, v_len, elem_width);
    printf("The execution took %u cycles, average %u cycles\n", timer_tot, timer_tot/measure_iterations);
    printf("The performance is %u load/1000cycle (%u%%o utilization).\n",
           performance, utilization);
  }

  // Wait for core 0 to finish displaying results
  mempool_barrier(num_cores);

  return 0;
}
