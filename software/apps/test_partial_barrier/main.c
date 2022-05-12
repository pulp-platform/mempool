// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

dump(wake_up, 0);

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if(core_id >= 5 && core_id < 35)
    mempool_wait(10);
  else if(core_id >= 35 && core_id < 130)
    mempool_wait(20);

  mempool_partial_barrier(core_id,5,125);

  dump_wake_up(core_id);

  if (core_id >= 5 && core_id < 120)
    mempool_wait(10);

  mempool_barrier(num_cores);

  return 0;
}
