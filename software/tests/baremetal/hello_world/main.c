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

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id != 0) {
    mempool_wfi();
  }

  printf("Core %3d says Hello!\n", core_id);
  wake_up(core_id + 1);

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
