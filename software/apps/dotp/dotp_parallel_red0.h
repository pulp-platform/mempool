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


/* Parallel dot-product */
void dotp_parallel_red0  ( int32_t* in_a,
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
  __atomic_fetch_add(&s[(core_id/STEP_CORES)*STEP], local_sum, __ATOMIC_RELAXED);
  mempool_stop_benchmark();

  mempool_start_benchmark();
  if ((NUM_CORES - 1) == __atomic_fetch_add(&barrier, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(barrier, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    uint32_t idx_red = 0;
    local_sum = 0;
    while(idx_red < N_BANK) {
//      int32_t red_1 = s[idx_red];
//      int32_t red_2 = s[idx_red+16];
//      int32_t red_3 = s[idx_red+32];
//      int32_t red_4 = s[idx_red+48];
//      local_sum += red_1;
//      local_sum += red_2;
//      local_sum += red_3;
//      local_sum += red_4;
      local_sum += s[idx_red];
      idx_red += STEP;
    }
    s[0] = local_sum;
    wake_up_all();
  }
  mempool_wfi();

//  if(core_id == 0) {
//    for(uint32_t i=1; i<NUM_CORES; i++) {
//      s[0] += s[i];
//    }
//  }
}

/* Parallel dot-product with loop unrolling */
void dotp_parallel_unrolled4_red0  (  int32_t* in_a,
                                      int32_t* in_b,
                                      int32_t* s,
                                      uint32_t Len,
                                      uint32_t nPE) {

  uint32_t const remainder = Len%4;
  uint32_t const idx_stop = Len - remainder;
  uint32_t core_id = mempool_get_core_id();
  int32_t local_sum_1 = 0;
  int32_t local_sum_2 = 0;
  int32_t local_sum_3 = 0;
  int32_t local_sum_4 = 0;

  uint32_t idx = core_id*4;
  while (idx< idx_stop) {
    int32_t in_a1 = in_a[idx];
    int32_t in_b1 = in_b[idx];
    int32_t in_a2 = in_a[idx+1];
    int32_t in_b2 = in_b[idx+1];
    int32_t in_a3 = in_a[idx+2];
    int32_t in_b3 = in_b[idx+2];
    int32_t in_a4 = in_a[idx+3];
    int32_t in_b4 = in_b[idx+3];
    local_sum_1 += in_a1*in_b1;
    local_sum_2 += in_a2*in_b2;
    local_sum_3 += in_a3*in_b3;
    local_sum_4 += in_a4*in_b4;
    idx+= N_BANK;
  }
  if (core_id == ((Len%N_BANK)/4)) {
    while(idx<Len){
      local_sum_1 += in_a[idx]*in_b[idx];
      idx++;
    }
  }
  local_sum_1 += local_sum_2;
  local_sum_3 += local_sum_4;
  local_sum_1 += local_sum_3;
  //s[core_id] = local_sum_1;
  __atomic_fetch_add(&s[core_id>>6], local_sum_1, __ATOMIC_RELAXED);
  mempool_barrier(NUM_CORES);

  if(core_id == 0) {
    for(uint32_t i=1; i<NUM_CORES; i++) {
      s[0] += s[i];
    }
  }
  mempool_barrier(NUM_CORES);
}
