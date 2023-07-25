// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Vaibhav Krishna, ETH Zurich
//         Sergio Mazzola, ETH Zurich

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

/* Settings */
#define PRINTF_VERBOSE 1

int main(){
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialization
  mempool_barrier_init(core_id);
  mempool_init(core_id);

  /* Systolic grid mapping */
  // stage_i = index of this PE's stage (FFT stage); ROW index
  // pe_i    = index of this PE in its stage; COLUMN index
  uint32_t stage_i = core_id % NUM_CORES_PER_TILE;
  uint32_t pe_i    = core_id / NUM_CORES_PER_TILE; // tile ID
  // NUM_CORES_PER_TILE is equal to NUM_STAGES, i.e. 4

  core_mapping[stage_i][pe_i] = core_id;
  mempool_barrier(num_cores);

  // Setup
  if(core_id == 0){
    #if PRINTF_VERBOSE
    printf("Initialize\n");
    #endif
    shuffling_order_calc();
  }
  mempool_barrier(num_cores);

  systolic_init(stage_i, pe_i);

  mempool_barrier(num_cores);

  for(int16_t i=core_id;i<2048;i+=num_cores)
    pSrc[i]=vector_inp[i];

  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("> Start\n");
  }

  //Start benchmark for all cores
  mempool_barrier(num_cores);
  mempool_start_benchmark();

  if (stage_i == 0) {
    systolic_first_fft_pe(stage_i, pe_i);
  } else if (stage_i == (NUM_STAGES-1)){
    systolic_end_pe(stage_i, pe_i, core_id);
  } else {
    systolic_mid_pe(stage_i, pe_i, core_id);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  // Print out benchmark
  if (core_id == 0) {
    // for (uint32_t i=0;i<(2*LEN_FFT);i++){
    //   if (abs((vector_output[i] - vector_res[i])) > TOLERANCE)
    //     printf("ERROR!!! Result[%d]: %6d Expected[%d]: %6d\n", i, vector_output[i], i,
    //            vector_res[i]);
    // }
    printf("> End\n");
  }

  mempool_barrier(num_cores);
  return 0;
}
