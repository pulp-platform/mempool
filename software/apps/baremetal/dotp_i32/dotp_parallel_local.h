// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/*
  Parallel dot-product with final reduction performed by multiple cores
  using atomic-fetch and adds to a single memory location.
   A) Parallelized workload
   B) Atomic fetch and add to a single memory location
   C) Barrier */

/*******************************************************/
/**                    MULTI-CORE                     **/
/*******************************************************/

/* Parallel dot-product */
void dotp_parallel_local(int32_t *in_a, int32_t *in_b, int32_t *s, uint32_t Len,
                         uint32_t nPE) {

  uint32_t const remainder = Len % 4;
  uint32_t const idx_stop = Len - remainder;
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  if (nPE == num_cores) {
    register int32_t local_sum = 0;
    uint32_t idx = core_id * 4;
    while (idx < idx_stop) {
      local_sum += in_a[idx] * in_b[idx];
      local_sum += in_a[idx + 1] * in_b[idx + 1];
      local_sum += in_a[idx + 2] * in_b[idx + 2];
      local_sum += in_a[idx + 3] * in_b[idx + 3];
      idx += N_BANK;
    }
    if (core_id == (Len % N_BANK) / 4) {
      while (idx < Len) {
        local_sum += in_a[idx] * in_b[idx];
        idx++;
      }
    }
    mempool_stop_benchmark();
    mempool_start_benchmark();
    __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
    mempool_log_barrier(2, core_id);
#else
    mempool_barrier(num_cores);
#endif
  } else {
    register int32_t local_sum = 0;
    uint32_t idx = core_id * 4;
    while (idx < idx_stop) {
      local_sum += in_a[idx] * in_b[idx];
      local_sum += in_a[idx + 1] * in_b[idx + 1];
      local_sum += in_a[idx + 2] * in_b[idx + 2];
      local_sum += in_a[idx + 3] * in_b[idx + 3];
      idx += N_BANK_PE;
    }
    if (core_id == (Len % N_BANK_PE) / 4) {
      while (idx < Len) {
        local_sum += in_a[idx] * in_b[idx];
        idx++;
      }
    }
    if (core_id < nPE) {
      mempool_stop_benchmark();
      mempool_start_benchmark();
    }
    __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
    mempool_log_partial_barrier(2, core_id, nPE);
#else
    mempool_barrier(num_cores);
#endif
  }
}

/* Parallel dot-product with loop unrolling */
void dotp_parallel_local_unrolled4(int32_t *in_a, int32_t *in_b, int32_t *s,
                                   uint32_t Len, uint32_t nPE) {

  uint32_t const remainder = Len % 4;
  uint32_t const idx_stop = Len - remainder;
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  register int32_t local_sum_1 = 0;
  register int32_t local_sum_2 = 0;
  register int32_t local_sum_3 = 0;
  register int32_t local_sum_4 = 0;

  if (nPE == num_cores) {
    uint32_t idx = core_id * 4;
    while (idx < idx_stop) {
      int32_t in_a1 = in_a[idx];
      int32_t in_b1 = in_b[idx];
      int32_t in_a2 = in_a[idx + 1];
      int32_t in_b2 = in_b[idx + 1];
      int32_t in_a3 = in_a[idx + 2];
      int32_t in_b3 = in_b[idx + 2];
      int32_t in_a4 = in_a[idx + 3];
      int32_t in_b4 = in_b[idx + 3];
      local_sum_1 += in_a1 * in_b1;
      local_sum_2 += in_a2 * in_b2;
      local_sum_3 += in_a3 * in_b3;
      local_sum_4 += in_a4 * in_b4;
      idx += N_BANK;
    }
    if (core_id == ((Len % N_BANK) / 4)) {
      while (idx < Len) {
        local_sum_1 += in_a[idx] * in_b[idx];
        idx++;
      }
    }
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_1 += local_sum_3;
    mempool_stop_benchmark();
    mempool_start_benchmark();
    __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
    mempool_log_barrier(2, core_id);
#else
    mempool_barrier(num_cores);
#endif
  } else {
    uint32_t idx = core_id * 4;
    while (idx < idx_stop) {
      int32_t in_a1 = in_a[idx];
      int32_t in_b1 = in_b[idx];
      int32_t in_a2 = in_a[idx + 1];
      int32_t in_b2 = in_b[idx + 1];
      int32_t in_a3 = in_a[idx + 2];
      int32_t in_b3 = in_b[idx + 2];
      int32_t in_a4 = in_a[idx + 3];
      int32_t in_b4 = in_b[idx + 3];
      local_sum_1 += in_a1 * in_b1;
      local_sum_2 += in_a2 * in_b2;
      local_sum_3 += in_a3 * in_b3;
      local_sum_4 += in_a4 * in_b4;
      idx += N_BANK_PE;
    }
    if (core_id == ((Len % N_BANK_PE) / 4)) {
      while (idx < Len) {
        local_sum_1 += in_a[idx] * in_b[idx];
        idx++;
      }
    }
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_1 += local_sum_3;
    mempool_stop_benchmark();
    mempool_start_benchmark();
    __atomic_fetch_add(&s[0], local_sum_1, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
    mempool_log_partial_barrier(2, core_id, nPE);
#else
    mempool_barrier(num_cores);
#endif
  }
}
