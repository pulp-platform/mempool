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
#define VERIFY_OUTPUT  1

/* Global variables */
// '2 *' for complex FFT: each of the 256 points is a complex number with 2 16-bit values
int16_t vector_input[2 * LEN_FFT] __attribute__((section(".l1")));
int16_t vector_output[2 * LEN_FFT] __attribute__((section(".l1")));

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

  core_mapping[stage_i][pe_i] = (uint16_t)core_id;
  mempool_barrier(num_cores);

  // Setup
  if(core_id == 0){
    #if PRINTF_VERBOSE
    printf("Initialize\n");
    #endif
    shuffling_order_calc();
  }

  // copy input data to L1
  for(uint32_t i = core_id; i < 2 * LEN_FFT; i+= num_cores)
    vector_input[i] = vector_inp[i];
  mempool_barrier(num_cores);

  systolic_init(stage_i, pe_i);
  mempool_barrier(num_cores);

  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("Start\n");
    #endif
  }
  mempool_barrier(num_cores);

  // Start benchmark for all cores
  mempool_start_benchmark();

  if (stage_i == 0) {
    systolic_first_fft_pe(pe_i);
  } else if (stage_i == (NUM_STAGES-1)){
    systolic_end_pe(pe_i, core_id);
  } else {
    systolic_mid_pe(stage_i, pe_i, core_id);
  }

  // Stop benchmark for all cores
  mempool_stop_benchmark();
  mempool_barrier(num_cores);

  if (core_id == 0) {
    #if PRINTF_VERBOSE
    printf("End\n");
    #endif

    // Verify result
    #if VERIFY_OUTPUT
    #if PRINTF_VERBOSE
    printf("Verifying output...\n");
    #endif
    uint32_t error_found = 0;
    // '2 *' for complex FFT: each of the 256 points is a complex number with 2 16-bit values
    for (uint32_t i = 0; i < (2 * LEN_FFT); i++){
      //printf("vector_output[%d] = %6d (expected = %6d)\n", i, vector_output[i], vector_res[i]);
      if (abs((vector_output[i] - vector_res[i])) > TOLERANCE) {
        #if PRINTF_VERBOSE
        printf("ERROR: vector_output[%d] = %6d, expected is %6d\n", i, vector_output[i], vector_res[i]);
        #endif
        error_found = 1;
      }
    }
    if (error_found)
      return -1;
    #endif
  }

  mempool_barrier(num_cores);
  return 0;
}
