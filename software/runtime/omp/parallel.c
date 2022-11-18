// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This file handles the (bare) PARALLEL construct.  */

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

event_t event;
work_t works;

void set_event(void (*fn)(void *), void *data, uint32_t nthreads) {
  uint32_t num_cores = mempool_get_core_count();
  event.fn = fn;
  event.data = data;
  if (nthreads == 0) {
    event.nthreads = num_cores;
    event.barrier = num_cores;
  } else {
    event.nthreads = nthreads;
    event.barrier = nthreads;
  }

  for (uint32_t i = 0; i < num_cores; i++) {
    event.thread_pool[i] = (i < event.nthreads) ? 1 : 0;
  }
}

void run_task(uint32_t core_id) {
  if (event.thread_pool[core_id]) {
    event.fn(event.data);
    __atomic_add_fetch(&event.barrier, -1, __ATOMIC_SEQ_CST);
  }
}

void GOMP_parallel_start(void (*fn)(void *), void *data,
                         unsigned int num_threads) {
  set_event(fn, data, num_threads);
  wake_up_all();
  mempool_wfi();
}

void GOMP_parallel_end(void) {
  uint32_t num_cores = mempool_get_core_count();
  while (event.barrier > 0) {
    mempool_wait(4 * num_cores);
  }
}

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"
void GOMP_parallel(void (*fn)(void *), void *data, unsigned int num_threads,
                   unsigned int flags) {
  uint32_t core_id = mempool_get_core_id();
  gomp_new_work_share();
  GOMP_parallel_start(fn, data, num_threads);
  run_task(core_id);
  GOMP_parallel_end();
}
#pragma GCC diagnostic pop

/* The public OpenMP API for thread and team related inquiries.  */
uint32_t omp_get_num_threads(void) { return event.nthreads; }

uint32_t omp_get_thread_num(void) { return mempool_get_core_id(); }
