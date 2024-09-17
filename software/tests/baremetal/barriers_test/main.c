// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "data_barriers_test.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

uint32_t volatile checksum __attribute__((section(".l1")));
uint32_t volatile countval __attribute__((section(".l1")));

int main() {

  uint32_t volatile core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);
  uint32_t __stride__, __offset__;
  if (core_id == 0) {
    __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
    __atomic_store_n(&countval, 0, __ATOMIC_RELAXED);
  }
  mempool_barrier(num_cores);

  // Central counter barrier
  __atomic_fetch_add(&checksum, core_id, __ATOMIC_RELAXED);
  countval = num_cores * (num_cores - 1) / 2;
  mempool_barrier(num_cores);
  if (core_id == 0) {
    if (checksum != countval) {
      return 1;
    } else {
      printf("SUM:   %d\n", checksum);
      printf("CHECK: %d\n", countval);
      __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
    }
  }
  mempool_barrier(num_cores);

  // Simple log2 barrier
  __atomic_fetch_add(&checksum, core_id, __ATOMIC_RELAXED);
  countval = num_cores * (num_cores - 1) / 2;
  mempool_log2_barrier(8, core_id);
  if (core_id == 0) {
    if (checksum != countval) {
      return 1;
    } else {
      printf("SUM:   %d\n", checksum);
      printf("CHECK: %d\n", countval);
      __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
    }
  }
  mempool_barrier(num_cores);

  // Simple logR barrier
  __atomic_fetch_add(&checksum, core_id, __ATOMIC_RELAXED);
  countval = num_cores * (num_cores - 1) / 2;
  mempool_logR_barrier(16, core_id, 4);
  if (core_id == 0) {
    if (checksum != countval) {
      return 1;
    } else {
      printf("SUM:   %d\n", checksum);
      printf("CHECK: %d\n", countval);
      __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
    }
  }
  mempool_barrier(num_cores);

  // Strided central-counter barrier
  __stride__ = 2;
  __offset__ = 8;
  if (core_id >= __offset__) {
    if (core_id % __stride__ == 0) {
      __atomic_fetch_add(&checksum, core_id, __ATOMIC_RELAXED);
      countval =
          (num_cores * (num_cores - 2) / 4) - __offset__ * (__offset__ - 2) / 4;
      mempool_strided_barrier(num_cores, __stride__, __offset__);
      if (core_id == __offset__) {
        if (checksum != countval) {
          return 1;
        } else {
          printf("SUM:   %d\n", checksum);
          printf("CHECK: %d\n", countval);
          __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
        }
      }
    }
  }
  mempool_barrier(num_cores);

  // Strided log2 barrier
  __stride__ = 2;
  __offset__ = 128;
  if (core_id >= __offset__) {
    if (core_id % __stride__ == 0) {
      __atomic_fetch_add(&checksum, core_id, __ATOMIC_RELAXED);
      countval =
          (num_cores * (num_cores - 2) / 4) - __offset__ * (__offset__ - 2) / 4;
      __sync_synchronize();
      mempool_strided_log2_barrier(4, core_id, __stride__, __offset__);
      if (core_id == __offset__) {
        if (checksum != countval) {
          return 1;
        } else {
          printf("SUM:   %d\n", checksum);
          printf("CHECK: %d\n", countval);
          __atomic_store_n(&checksum, 0, __ATOMIC_RELAXED);
        }
      }
    }
  }
  mempool_barrier(num_cores);

#if defined(DELAY)
  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_barrier(num_cores);

  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_log2_barrier(8, core_id);

  uint32_t delay = core_delays[core_id];
  mempool_wait(delay);
  mempool_logR_barrier(16, core_id, 4);

#endif

  return 0;
}
