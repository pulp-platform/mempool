// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_barriers_test.h"
#define LIN_LOG_BARRIER_DELAY

dump(id, 1);

int main() {

  uint32_t volatile core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  mempool_barrier(num_cores);

#if defined(PLAIN_BARRIER)
  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#elif defined(LOG_BARRIER)
  mempool_start_benchmark();
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();

#elif defined(PLAIN_BARRIER_DELAY)
  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#elif defined(LOG_BARRIER_DELAY)
  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_start_benchmark();
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();

#elif defined(LIN_LOG_BARRIER_DELAY)
  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_start_benchmark();
  mempool_linlog_barrier(4, core_id);
  mempool_stop_benchmark();

  dump_id(core_id);

#endif

  return 0;
}
