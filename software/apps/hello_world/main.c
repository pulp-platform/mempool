// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Matheus Cavalcante, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

volatile uint32_t atomic __attribute__((section(".l2"))) = NUM_CORES;

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);
  if (core_id == 0) {
    atomic = 0;
  }
  mempool_barrier(num_cores, num_cores * 4);

  while (atomic != core_id)
    mempool_wait(2 * num_cores);

  printf("Core %d says Hello!\n", core_id);
  atomic++;

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);
  return 0;
}
