// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_dotp_f16.h"
#define NUM_BANKS (NUM_CORES * BANKING_FACTOR)
// #define SINGLE_CORE_REDUCTION
#define BINARY_REDUCTION

// Vectors for kernel computation
__fp16 l1_A[LEN] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
__fp16 l1_B[LEN] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
uint32_t red_barrier[NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
__fp16 sum[2 * NUM_BANKS]
    __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

#include "baremetal/mempool_dotp_f16.h"

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time_init, time_end;
  mempool_barrier_init(core_id);

  time_init = 0;
  time_end = 0;
  if (core_id == 0) {
    dma_memcpy_blocking(l1_A, l2_A, LEN * sizeof(int16_t));
    dma_memcpy_blocking(l1_B, l2_B, LEN * sizeof(int16_t));
  }
  for (uint32_t k = core_id; k < NUM_BANKS; k += num_cores) {
    sum[k] = 0;
    red_barrier[k] = 0;
  }
  mempool_barrier(num_cores);

  //  // SINGLE-CORE
  //  time_init = mempool_get_timer();
  //  dotp_f16s(l1_A, l1_B, sum, LEN);
  //  // dotp_f16s_unrolled4(l1_A, l1_B, sum, LEN);
  //  time_end = mempool_get_timer();

  //  // PARALLEL
  //  time_init = mempool_get_timer();
  //  dotp_f16vecp_unrolled4(l1_A, l1_B, sum, LEN, num_cores);
  //  // dotp_f16p(l1_A, l1_B, sum, LEN, num_cores);
  //  time_end = mempool_get_timer();

  // PARALLEL, LOCAL ACCESSES
  time_init = mempool_get_timer();
  dotp_f16vecp_local_unrolled4(l1_A, l1_B, sum, LEN);
  time_end = mempool_get_timer();

  // Check results
  mempool_barrier(num_cores);
  if (core_id == 0) {
    uint32_t clock_cycles = (time_end - time_init);
    printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
    printf("Result ==> %x\n", *(uint32_t *)&sum[0]);
    printf("Check  ==> %x\n\n", *(uint32_t *)&l2_C);
  }
  mempool_barrier(num_cores);

  return 0;
}
