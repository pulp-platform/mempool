// Copyright 2022 ETH Zurich and University of Bologna.
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
#include "xpulp/builtins_v2.h"

#include "data_chest_q16.h"
#include "chest_q16s.h"

#define SINGLE

int16_t PilotTX_l1[2*N_TX*N_SAMPLES] __attribute__((aligned(N_TX*N_SAMPLES), section(".l1")));
int16_t PilotRX_l1[2*N_RX*N_SAMPLES] __attribute__((aligned(N_TX*N_SAMPLES), section(".l1")));
int16_t HEST_l1[2*N_RX*N_TX*N_SAMPLES] __attribute__((aligned(N_TX*N_SAMPLES), section(".l1")));

void initialize_vector(int16_t  *pSrc_l2, int16_t  *pDst_l1, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for(uint32_t i = core_id; i < N_el; i += num_cores) {
    pDst_l1[i] = (int16_t)pSrc_l2[i];
  }
  mempool_barrier(num_cores);
  return;
}

void zeros(int16_t  *pSrc_l1, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  for(uint32_t i = core_id; i < N_el; i += num_cores) {
    pSrc_l1[i] = (int16_t)0;
  }
  mempool_barrier(num_cores);
  return;
}

void check_result(int16_t  *pRes, int16_t *pExp, uint32_t N_el) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if(core_id == 0) {
    for(uint32_t i = 0; i < N_el; i++) {
      if (pExp[i] != pRes[i]) {
        printf("ERROR: Exp[%6d]=%6d Res[%6d]=%6d\n", i, pExp[i], i, pRes[i]);
      }
    }
  }
  mempool_barrier(num_cores);
  return;
}

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  initialize_vector(PilotTX, PilotTX_l1, 2*(N_TX*N_SAMPLES));
  initialize_vector(PilotRX, PilotRX_l1, 2*(N_RX*N_SAMPLES));
  zeros(HEST_l1, 2*(N_RX*N_TX*N_SAMPLES));

  #ifdef SINGLE
  if (core_id == 0) {
    mempool_chest_q16s_unrolled4(HEST_l1, PilotRX_l1, PilotTX_l1, N_RX, N_TX, N_SAMPLES);
    mempool_start_benchmark();
    mempool_chest_q16s_unrolled4_xpulpv2(HEST_l1, PilotRX_l1, PilotTX_l1, N_RX, N_TX, N_SAMPLES);
    // mempool_chest_q16s_radix4(HEST_l1, PilotRX_l1, PilotTX_l1, N_RX, N_TX, N_SAMPLES);
    mempool_stop_benchmark();
  }
  #endif
  mempool_barrier(num_cores);

  //check_result(HEST_l1, HEST, 2*N_RX*N_TX*N_SAMPLES);

  return 0;
}
