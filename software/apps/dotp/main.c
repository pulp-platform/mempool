// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "define.h"

#if defined(SINGLE) || defined(SINGLE_UNROLLED)
#include "dotp_single.h"
#endif

#if defined(PARALLEL) || defined(PARALLEL_UNROLLED)
#include "dotp_parallel.h"
#endif

#if defined(PARALLEL_RED0) || defined(PARALLEL_UNROLLED_RED0)
#include "dotp_parallel_red0.h"
#endif

#if defined(PARALLEL_REDTREE) || defined(PARALLEL_UNROLLED_REDTREE)
#include "dotp_parallel_redtree.h"
#endif

void initialize_custom_barriers(uint32_t volatile * barrier_global, uint32_t volatile * barrier_local) {
  *barrier_global = 0;
  for(uint32_t i = 0; i<N_BANK; i++) {
    barrier_local[i] = 0;
  }
}

void init_vectors( int32_t* in_a, int32_t* in_b, int32_t* s,
                   int32_t* p_result, int32_t* p_check, uint32_t N_vect) {
  *p_result = 0;
  *p_check = 0;
  *s = 0;
  uint32_t split = N_vect/NUM_CORES;
  uint32_t j = 0;
  while(j<NUM_CORES) {
    uint32_t MAX = (j+1)*split > N_vect? N_vect : (j+1)*split;
    for(uint32_t i = j*split; i < MAX; i++) {
      int32_t a = (int32_t)(i - 6);
      int32_t b = i%4 == 0? -1 : 1;
      in_a[i] = a;
      in_b[i] = b;
      *p_check = *p_check + (int32_t) (a*b);
    }
    j++;
  }
}

void init_vectors_red0(   int32_t* in_a, int32_t* in_b, int32_t* s,
                              int32_t* p_result, int32_t* p_check, uint32_t N_vect) {
  *p_result = 0;
  *p_check = 0;
  uint32_t split = N_vect/NUM_CORES;
  uint32_t j = 0;
  while(j<NUM_CORES) {
    uint32_t MAX = (j+1)*split > N_vect? N_vect : (j+1)*split;
    for(uint32_t i = j*split; i < MAX; i++) {
      int32_t a = (int32_t)(i - 20);
      int32_t b = i%4 == 0? -1 : 1;
      in_a[i] = a;
      in_b[i] = b;
      *p_check = *p_check + (int32_t) (a*b);
    }
    j++;
  }
 for(uint32_t k=0; k<N_BANK; k++) {
   s[k] = 0;
 }

}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t time_init, time_end;

  //initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id == 0) {
  	error = 0;
    time_init = 0;
    time_end = 0;
    #if defined(PARALLEL_RED0) || defined(PARALLEL_UNROLLED_RED0) || defined(PARALLEL_REDTREE) || defined(PARALLEL_UNROLLED_REDTREE)
    initialize_custom_barriers(&barrier_global, barrier_local);
    init_vectors_red0(vector_a, vector_b, sum, &result, &check, N);
    #else
    init_vectors(vector_a, vector_b, &sum, &result, &check, N);
    #endif
  }
  mempool_barrier(NUM_CORES); // wait until all cores have finished

  // Kernel execution

  #ifdef SINGLE
    time_init = mempool_get_timer();
    dotp_single(vector_a, vector_b, &sum, N, core_id);
    time_end = mempool_get_timer();
  #endif

  #ifdef SINGLE_UNROLLED
    //time_init = mempool_get_timer();
    dotp_single_unrolled4(vector_a, vector_b, &sum, N, core_id);
    //time_end = mempool_get_timer();
  #endif

  /* A) Parallelized workload
     B) Atomic fetch and add to a single memory location
     C) Barrier */

  #ifdef PARALLEL
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel(vector_a, vector_b, &sum, N, core_id);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  #ifdef PARALLEL_UNROLLED
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel_unrolled4(vector_a, vector_b, &sum, N, core_id);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  /* A) Parallelized workload
     B) Atomic fetch and add to local memory banks
     C) Barrier
     D) Final reduction by core 0 incorporated in a barrier */

  #ifdef PARALLEL_RED0
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel_red0(vector_a, vector_b, sum, N, core_id, &barrier_global);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  #ifdef PARALLEL_UNROLLED_RED0
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel_unrolled4_red0(vector_a, vector_b, sum, N, core_id, &barrier_global);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  /* A) Parallelized workload
     B) Nested set of barriers: reduction is performed in a logarithmic tree. */

  #ifdef PARALLEL_REDTREE
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel_redtree(vector_a, vector_b, sum, N, core_id);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  #ifdef PARALLEL_UNROLLED_REDTREE
    time_init = mempool_get_timer();
    mempool_start_benchmark();
    dotp_parallel_redtree_unrolled(vector_a, vector_b, sum, N, core_id);
    mempool_stop_benchmark();
    time_end = mempool_get_timer();
  #endif

  // Check results
  if (core_id == 0) {
    uint32_t clock_cycles = (time_end-time_init);
    #if defined(PARALLEL_RED0) || defined(PARALLEL_UNROLLED_RED0) || defined(PARALLEL_REDTREE) || defined(PARALLEL_UNROLLED_REDTREE)
    result = sum[0];
    #else
    result = sum;
    #endif
    printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
		printf("Result ==> %d\n", result);
		printf("Check  ==> %d\n\n", check);
  }
  mempool_barrier(NUM_CORES);

  return error;
}
