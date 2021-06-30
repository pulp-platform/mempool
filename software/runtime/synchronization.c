// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdbool.h>
#include <stdint.h>

#include "runtime.h"
#include "synchronization.h"

uint32_t volatile barrier __attribute__((section(".l1")));
uint32_t volatile barrier_iteration __attribute__((section(".l1")));
uint32_t volatile barrier_init __attribute__((section(".l2"))) = 0;

void mempool_barrier_init(uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    barrier = 0;
    barrier_iteration = 0;
    barrier_init = 1;
  } else {
    while (!barrier_init)
      mempool_wait(2 * num_cores);
  }
}

void mempool_barrier_init_sleep(uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    // Give other cores time to go to sleep
    mempool_wait(4 * num_cores);
    barrier = 0;
    barrier_iteration = 0;
    barrier_init = 1;
    wake_up((uint32_t)-1);
  } else {
    mempool_wfi();
  }
}

void mempool_barrier(uint32_t num_cores, uint32_t cycles) {
  // Remember previous iteration
  uint32_t iteration_old = barrier_iteration;

  // Increment the barrier counter
  if ((num_cores - 1) == __atomic_fetch_add(&barrier, 1, __ATOMIC_SEQ_CST)) {
    barrier = 0;
    __atomic_fetch_add(&barrier_iteration, 1, __ATOMIC_SEQ_CST);
  } else {
    // Some threads have not reached the barrier --> Let's wait
    while (iteration_old == barrier_iteration)
      mempool_wait(cycles);
  }
}
