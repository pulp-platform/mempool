// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Vaibhav Krishna, ETH Zurich

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
#include "systolic/fft_256_xqueue.h"

int main(){
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t tile_id = core_id / 4;


  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id);

  // Allocate systolic grid mapping
  uint32_t stage_idx;
  uint32_t idx_in_stage;

  stage_idx    = core_id % 4;
  idx_in_stage = tile_id;

  mempool_barrier(num_cores);


  tile_mapping[stage_idx*PE_PER_STAGE + idx_in_stage] = tile_id;
  core_mapping[stage_idx*PE_PER_STAGE + idx_in_stage] = core_id;

  mempool_barrier(num_cores);

  //Setup
  if(core_id == 0){
    printf(">Initialize\n");
    shuffling_order_calc();
    systolic_init();
  }

  for(int16_t i=core_id;i<2048;i+=num_cores)
    pSrc[i]=vector_inp[i];

  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("> Start\n");
  }

  //Start benchmark for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  if (stage_idx == 0) {
    systolic_first_fft_pe(stage_idx, idx_in_stage);
  } else if (stage_idx == (NUM_STAGE-1)){
    systolic_end_pe(stage_idx, idx_in_stage, core_id);
  } else {
    systolic_mid_pe(stage_idx, idx_in_stage, core_id);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    // for (uint32_t i=0;i<(2*FFTLEN);i++){
    //   if (abs((vector_output[i] - vector_res[i])) > TOLERANCE)
    //     printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, vector_output[i], i,
    //            vector_res[i]);
    // }
    printf("> End\n");
  }

  mempool_barrier(num_cores);
  return 0;
}
