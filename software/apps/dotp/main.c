// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/dotp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N (1024 * 32)

dump(time, 0);

int32_t vec_a[N] __attribute__((section(".l1_prio")));
int32_t vec_b[N] __attribute__((section(".l1_prio")));

volatile int32_t vec_a_l2[N] __attribute__((section(".l2")));
volatile int32_t vec_b_l2[N] __attribute__((section(".l2")));

void init_vector(volatile int32_t *vec, uint32_t size, uint32_t core_id,
                 uint32_t num_cores) {
  const int32_t unroll = 4;
  for (int32_t i = unroll * (int32_t)core_id; i < (int32_t)size;
       i += unroll * (int32_t)num_cores) {
    vec[i + 0] = i - (int32_t)num_cores;
    vec[i + 1] = -i - (int32_t)num_cores;
    vec[i + 2] = i + (int32_t)num_cores;
    vec[i + 3] = -i + (int32_t)num_cores;
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  int32_t *c = (int32_t *)(128 * 1024);
  int32_t *dotp_barrier_a = (int32_t *)(64 * 1024);
  int32_t *dotp_barrier_b = (int32_t *)(192 * 1024);

  // Initialize img
  init_vector(vec_a, N, core_id, num_cores);
  init_vector(vec_b, N, core_id, num_cores);
  mempool_barrier(num_cores);
  if (core_id == 0) {
    *c = 0;
    *dotp_barrier_a = 0;
    *dotp_barrier_b = 0;
    dma_memcpy_blocking(vec_a_l2, vec_a, N * sizeof(int32_t));
    dma_memcpy_blocking(vec_b_l2, vec_b, N * sizeof(int32_t));
  }

  // Vectors are initialized --> Start calculating
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);
  uint32_t start = mempool_get_timer();
  mempool_start_benchmark();
  // dotp_parallel((const int32_t *)vec_a, (const int32_t *)vec_b, N, c,
  // core_id, num_cores);
  dotp_parallel_dma((const int32_t *)vec_a, (const int32_t *)vec_b, N,
                    (const int32_t *)vec_a_l2, (const int32_t *)vec_b_l2, N, c,
                    core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  uint32_t stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

  // Hot cache
  start = mempool_get_timer();
  mempool_start_benchmark();
  // dotp_parallel((const int32_t *)vec_a, (const int32_t *)vec_b, N, c,
  // core_id,
  //               num_cores);
  dotp_parallel_dma((const int32_t *)vec_a, (const int32_t *)vec_b, N,
                    (const int32_t *)vec_a_l2, (const int32_t *)vec_b_l2, N, c,
                    core_id, num_cores);
  mempool_stop_benchmark();
  if (core_id == 44) {
    dump_time(mempool_get_timer() - start);
  }
  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  stop = mempool_get_timer();
  if (core_id == 44) {
    dump_time(stop - start);
  }

  // Check result
  // TODO

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return 0;
}
