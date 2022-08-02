// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

uint32_t *lock;
uint32_t result;

void parallel_critical_manual() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t islocked;

  mempool_timer_t cycles = mempool_get_timer();
  mempool_start_benchmark();

  islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  while (islocked) {
    mempool_wait(NUM_CORES);
    islocked = __atomic_fetch_or(lock, 1, __ATOMIC_SEQ_CST);
  }

  result += 100;

  __atomic_fetch_and(lock, 0, __ATOMIC_SEQ_CST);

  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

  mempool_barrier(num_cores);

  if (core_id == 0) {
    printf("Manual Critical Result: %d\n", result);
    printf("Manual Critical Duration: %d\n", cycles);
  }
}

void omp_parallel_critical() {
  uint32_t num_cores = mempool_get_core_count();

#pragma omp parallel num_threads(num_cores)
  {
    mempool_timer_t cycles = mempool_get_timer();
    mempool_start_benchmark();

#pragma omp critical
    { result += 100; }

    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    mempool_barrier(num_cores);

#pragma omp master
    {
      printf("OMP Critical Result: %d\n", result);
      printf("OMP Critical Duration: %d\n", cycles);
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    printf("Initialize\n");
    *lock = 0;
    result = 0;
  }

  mempool_barrier(num_cores);
  parallel_critical_manual();
  mempool_barrier(num_cores);

  result = 0;

  /*  OPENMP IMPLEMENTATION  */

  if (core_id == 0) {
    mempool_wait(4 * num_cores);
    omp_parallel_critical();
    mempool_wait(100 * num_cores);
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }
  return 0;
}
