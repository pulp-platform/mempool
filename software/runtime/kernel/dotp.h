// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the dot product kernel
 */

#pragma once
#include "dma.h"
#include "runtime.h"

// Must match the unroll factor in the code
#define DOTP_UNROLL (4)

void dotp_parallel(const int32_t *a, const int32_t *b, uint32_t N, int32_t *c,
                   uint32_t core_id, uint32_t num_cores) {
  int32_t tmp_sum[DOTP_UNROLL] = {0, 0, 0, 0};
  for (uint32_t i = DOTP_UNROLL * core_id; i < N;
       i += DOTP_UNROLL * num_cores) {
    tmp_sum[0] += a[i + 0] * b[i + 0];
    tmp_sum[1] += a[i + 1] * b[i + 1];
    tmp_sum[2] += a[i + 2] * b[i + 2];
    tmp_sum[3] += a[i + 3] * b[i + 3];
  }
  int32_t sum = tmp_sum[0];
  sum += tmp_sum[1];
  sum += tmp_sum[2];
  sum += tmp_sum[3];
  __atomic_fetch_add(c, sum, __ATOMIC_RELAXED);
}

void dotp_parallel_dma(const int32_t *a, const int32_t *b, uint32_t N,
                       const int32_t *a_remote, const int32_t *b_remote,
                       uint32_t N_remote, int32_t *c, uint32_t core_id,
                       uint32_t num_cores) {
  int32_t *dotp_barrier_a = (int32_t *)(64 * 1024);
  int32_t *dotp_barrier_b = (int32_t *)(192 * 1024);
  int32_t tmp_sum[DOTP_UNROLL] = {0, 0, 0, 0};

  uint32_t first = 0;
  uint32_t last = 2 * num_cores;
  int last_round = 2;

  // Initial setup
  if (core_id == 0) {
    wake_up_all();
  }

  for (int round = 0; round < last_round; ++round) {
    // Barrier, launch DMA for next iteration
    mempool_wfi();
    int bar = __atomic_fetch_add(dotp_barrier_a, 2, __ATOMIC_RELAXED);
    // Are we the first to reach the next round?
    if (bar == first) {
      dma_wait();
      dma_memcpy_nonblocking(a, a_remote, N * sizeof(int32_t));
      dma_memcpy_nonblocking(b, b_remote, N * sizeof(int32_t));
      bar = __atomic_fetch_add(dotp_barrier_a, 2, __ATOMIC_RELAXED);
    }
    // Are we the last one?
    if (bar == last) {
      *dotp_barrier_a = 0;
      if (round != last_round - 1) {
        wake_up_all();
      }
    }

    for (uint32_t i = DOTP_UNROLL * core_id; i < N;
         i += DOTP_UNROLL * num_cores) {
      tmp_sum[0] += a[i + 0] * b[i + 0];
      tmp_sum[1] += a[i + 1] * b[i + 1];
      tmp_sum[2] += a[i + 2] * b[i + 2];
      tmp_sum[3] += a[i + 3] * b[i + 3];
    }
  }
  int32_t sum = tmp_sum[0];
  sum += tmp_sum[1];
  sum += tmp_sum[2];
  sum += tmp_sum[3];
  __atomic_fetch_add(c, sum, __ATOMIC_RELAXED);
}
