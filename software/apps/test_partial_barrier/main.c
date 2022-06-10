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

dump(cores_awake, 1);

int main() {

  uint32_t volatile core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id >= 65 && core_id < 98)
    mempool_wait(10);
  else if (core_id >= 98 && core_id < 126)
    mempool_wait(20);
  mempool_partial_barrier(core_id, 65, 61, 0);
  // dump_cores_awake(core_id);
  if (core_id >= 65 && core_id < 126)
    mempool_wait(10);
  mempool_barrier(num_cores);

  mempool_partial_barrier(core_id, 0, 64, 1);
  mempool_partial_barrier(core_id, 64, 64, 2);
  mempool_partial_barrier(core_id, 128, 64, 3);
  mempool_partial_barrier(core_id, 192, 64, 4);
  dump_cores_awake(core_id);
  mempool_barrier(num_cores);

  mempool_partial_barrier(core_id, 64 * (core_id / 64), 64, 5);
  mempool_partial_barrier(core_id, 32 * (core_id / 32), 32, 6);
  mempool_partial_barrier(core_id, 16 * (core_id / 16), 16, 7);
  dump_cores_awake(core_id);
  mempool_barrier(num_cores);

  mempool_log_partial_barrier(2, core_id, 64);
  mempool_log_partial_barrier(2, core_id, 32);
  mempool_log_partial_barrier(2, core_id, 16);
  dump_cores_awake(core_id);
  mempool_barrier(num_cores);

  return 0;
}
