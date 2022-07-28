// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* Parallel dot-product */
void dotp_parallel_trivial (  int32_t* in_a,
                              int32_t* in_b,
                              int32_t* s,
                              uint32_t Len,
                              uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;

  register int32_t local_sum = 0;
  register int32_t a, b;
  for(uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    local_sum += a * b;
  }
  mempool_stop_benchmark();
  mempool_start_benchmark();
  __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
  #ifdef LOG_BARRIERS
    mempool_log_barrier(2, core_id);
  #else
    mempool_barrier(NUM_CORES);
  #endif
}

/* Parallel dot-product */
void dotp_parallel_trivial_unrolled4 (	int32_t* in_a,
                            						int32_t* in_b,
                            						int32_t* s,
                            						uint32_t Len,
                                        uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t reminder = step % 4;
  uint32_t i;

  register int32_t a0, b0, a1, b1, a2, b2, a3, b3;
  register int32_t local_sum0 = 0;
  register int32_t local_sum1 = 0;
  register int32_t local_sum2 = 0;
  register int32_t local_sum3 = 0;
	for(i = core_id * step; i < core_id * step + step - reminder; i += 4) {
    a0 = in_a[i];
    b0 = in_b[i];
    a1 = in_a[i + 1];
    b1 = in_b[i + 1];
    a2 = in_a[i + 2];
    b2 = in_b[i + 2];
    a3 = in_a[i + 3];
    b3 = in_b[i + 3];
		local_sum0 += a0 * b0;
    local_sum1 += a1 * b1;
    local_sum2 += a2 * b2;
    local_sum3 += a3 * b3;
  }
  while (i < step) {
    a0 = in_a[i];
    b0 = in_b[i];
    local_sum0 += a0 * b0;
    i++;
  }
  local_sum0 += local_sum1;
  local_sum2 += local_sum3;
  local_sum0 += local_sum2;
  mempool_barrier(NUM_CORES);

  mempool_stop_benchmark();
  mempool_start_benchmark();
  __atomic_fetch_add(&s[0], local_sum0, __ATOMIC_RELAXED);
  #ifdef LOG_BARRIERS
    mempool_log_barrier(2, core_id);
  #else
    mempool_barrier(NUM_CORES);
  #endif
}
