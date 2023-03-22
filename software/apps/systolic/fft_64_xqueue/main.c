// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Vaibhav Krishna, ETH Zurich
// Radix-4 64-point systolic FFT

#include <stdint.h>
#include <string.h>
#include <stdlib.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"
#include "data_cfftq16.h"
#include "mempool_cfft_q16_twiddleCoef.h"
#include "systolic/fft_64_xqueue.h"

uint32_t *tile_mapping;
uint32_t *core_mapping;
uint32_t *shuffling_order;
int16_t  *vector_output;

int main(){
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t tile_id = core_id / 4;


  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id);

  // Allocate systolic grid mapping
  if (core_id == 0) {
    shuffling_order = (uint32_t *)simple_malloc(64 * NUM_STAGE * sizeof(uint32_t));
    tile_mapping = (uint32_t *)simple_malloc(64 * sizeof(uint32_t));
    core_mapping = (uint32_t *)simple_malloc(64 * sizeof(uint32_t));
    vector_output= (int16_t *)simple_malloc(128 * sizeof(int16_t));
  }

  uint32_t stage_idx;
  uint32_t idx_in_stage;
  if (core_id < 64){
    stage_idx    = core_id % 4;
    idx_in_stage = tile_id;
  }

  mempool_barrier(num_cores);

  if(core_id < 64){
    tile_mapping[stage_idx*PE_PER_STAGE + idx_in_stage] = tile_id;
    core_mapping[stage_idx*PE_PER_STAGE + idx_in_stage] = core_id;
  }

  mempool_barrier(num_cores);

  //Setup
  if(core_id == 0){
    printf(">Initialize\n");
    shuffling_order_calc(shuffling_order);
    systolic_init(tile_mapping, core_mapping, shuffling_order);
  }

  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("> Start\n");
  }

  //Start benchmark for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  if(core_id < 64){
    if (stage_idx == 0) {
      systolic_front_pe(idx_in_stage);
    } else if (stage_idx == 1){
      systolic_first_fft_pe(stage_idx, idx_in_stage);
    } else if (stage_idx == 2){
      systolic_mid_pe(stage_idx, idx_in_stage);
    } else {
      systolic_end_pe(idx_in_stage,vector_output,shuffling_order);
    }
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    for (uint32_t i=0;i<(2*FFTLEN);i++){
      if (abs((vector_output[i] - vector_res[i])) > TOLERANCE)
        printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, vector_output[i], i,
               vector_res[i]);
    }
    printf("> End\n");
  }

  mempool_barrier(num_cores);
  return 0;
}
