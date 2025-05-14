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

uint32_t *checksum;

int main() {

  uint32_t volatile core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  if (core_id == 0) {
    *checksum = 0;
  }
  mempool_barrier(num_cores);

#if defined(PLAIN_BARRIER)
  __atomic_fetch_add(checksum, 1U, __ATOMIC_RELAXED);
  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  if (*checksum < num_cores)
    return 1;

#elif defined(LOG_BARRIER)
  __atomic_fetch_add(checksum, 1U, __ATOMIC_RELAXED);
  mempool_start_benchmark();
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
  if (*checksum < num_cores)
    return 1;

#elif defined(PLAIN_BARRIER_DELAY)
  int32_t delay = l2_delays[core_id];
  mempool_wait((uint32_t)delay);
  __atomic_fetch_add(checksum, 1U, __ATOMIC_RELAXED);
  mempool_start_benchmark();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  if (*checksum < num_cores)
    return 1;

#elif defined(LOG_BARRIER_DELAY)
  int32_t delay = l2_delays[core_id];
  mempool_wait((uint32_t)delay);
  __atomic_fetch_add(checksum, 1U, __ATOMIC_RELAXED);
  mempool_start_benchmark();
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
  if (*checksum < num_cores)
    return 1;

#elif defined(LIN_LOG_BARRIER_DELAY)
  int32_t delay = l2_delays[core_id];
  mempool_wait((uint32_t)delay);
  __atomic_fetch_add(checksum, 1U, __ATOMIC_RELAXED);
  mempool_start_benchmark();
  mempool_linlog_barrier(4, core_id);
  mempool_stop_benchmark();
  if (*checksum < num_cores)
    return 1;

#endif

  return 0;
}
