// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/*
  Parallel dot-product with atomic fetch and add towards local memory
  locations and final reduction by a single core. The cores write in
  memory banks separated by a "step".
    A) Parallelized workload
    B) Atomic fetch and add to local memory banks
    C) Barrier
    D) Final reduction by core 0 incorporated in a barrier */

/*******************************************************/
/**                    MULTI-CORE                     **/
/*******************************************************/

void mempool_log_reduction(int32_t * sum, uint32_t volatile step, uint32_t core_id, uint32_t num_cores);


/* Parallel dot-product */
void dotp_parallel_redtree  ( int32_t* in_a,
                              int32_t* in_b,
                              int32_t* s,
                              uint32_t Len,
                              uint32_t nPE) {

  uint32_t const remainder = Len%4;
  uint32_t const idx_stop = Len - remainder;
  uint32_t core_id = mempool_get_core_id();
  int32_t local_sum = 0;

  uint32_t idx = core_id*4;
  while (idx < idx_stop) {
    local_sum += in_a[idx]*in_b[idx];
    local_sum += in_a[idx+1]*in_b[idx+1];
    local_sum += in_a[idx+2]*in_b[idx+2];

    local_sum += in_a[idx+3]*in_b[idx+3];
    idx+= N_BANK;
  }
  if ( core_id == (Len%N_BANK)/4 ) {
    while(idx < Len){
      local_sum += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  s[core_id*4] = local_sum; //Each core is storing locally
  mempool_stop_benchmark();
  mempool_start_benchmark();
  mempool_log_reduction(s, 2, core_id, NUM_CORES);
}

void dotp_parallel_redtree_unrolled  (  int32_t* in_a,
                                        int32_t* in_b,
                                        int32_t* s,
                                        uint32_t Len,
                                        uint32_t nPE) {

  uint32_t const remainder = Len % 4;
  uint32_t const idx_stop = Len - remainder;
  uint32_t core_id = mempool_get_core_id();
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;

  uint32_t idx = core_id*4;
  while (idx < idx_stop){
    int32_t in_a1 = in_a[idx];
    int32_t in_b1 = in_b[idx];
    int32_t in_a2 = in_a[idx+1];
    int32_t in_b2 = in_b[idx+1];
    int32_t in_a3 = in_a[idx+2];
    int32_t in_b3 = in_b[idx+2];
    int32_t in_a4 = in_a[idx+3];
    int32_t in_b4 = in_b[idx+3];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2 * in_b2;
    local_sum_3 += in_a3 * in_b3;
    local_sum_4 += in_a4 * in_b4;
    idx += N_BANK;
  }
  if (core_id == ((Len % N_BANK) / 4)) {
    while(idx < Len){
      local_sum_1 += in_a[idx] * in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;
  s[core_id * 4] = local_sum_1; //Each core is storing locally
  mempool_stop_benchmark();
  mempool_start_benchmark();
  mempool_log_reduction(s, 2, core_id, NUM_CORES);
}

void mempool_log_reduction(int32_t * sum, uint32_t volatile step, uint32_t core_id, uint32_t num_cores){

  uint32_t idx_sum, idx = (step * (core_id / step)) * 4;
  uint32_t next_step, previous_step;
  int32_t local_sum;

  previous_step = step >> 1;
  if ((step - previous_step) == __atomic_fetch_add(&log_barrier[idx + previous_step - 1], previous_step, __ATOMIC_RELAXED)){

    local_sum = 0;
    idx_sum = idx;
    while(idx_sum < idx + step * 4) {
      local_sum += sum[idx_sum];
      idx_sum += previous_step * 4;
    }
    sum[idx] = local_sum;

    next_step = step << 1;
    __atomic_store_n(&log_barrier[idx + previous_step - 1], 0, __ATOMIC_RELAXED);
    if (num_cores == step){
      sum[0] = sum[idx];
      __sync_synchronize(); // Full memory barrier
      wake_up_all();
      mempool_wfi();
    } else {
      mempool_log_reduction(barrier, sum, next_step, core_id, num_cores);
    }

  }
  else
    mempool_wfi();

}
