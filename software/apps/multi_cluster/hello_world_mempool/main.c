// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Matheus Cavalcante, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "flex_runtime.h"
#include "flex_printf.h"

volatile uint32_t turn __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  flex_barrier_xy_init();

  if (core_id == 0)
    turn = 0;

  while (core_id != turn) {
    mempool_wfi();
  }

  printf("Core %3d says Hello!\n", core_id);
  turn++;
  wake_up_all();

  // wait until all cores have finished
  while (num_cores != turn) {
    mempool_wfi();
  }

  
  mempool_barrier(num_cores); // Equivalent to flex_intra_cluster_sync()
  flex_global_barrier_xy(); // Optional
  // flex_eoc(0);
  return 0;
}