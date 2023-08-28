// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

uint32_t volatile sleep1 __attribute__((section(".l1")));
uint32_t volatile sleep2 __attribute__((section(".l1")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id);
  if (core_id == 0) {
    sleep1 = 0;
    sleep2 = 0;
  }
  mempool_barrier(num_cores);

  /* WAKE-UP ALL TEST */

  if (core_id % 4 == 0) {
    if (core_id == 0) {
      set_wake_up_stride(4U);
      set_wake_up_offset(0U);
    }
    if ((num_cores / 4 - 1) ==
        __atomic_fetch_add(&sleep1, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep1, 0, __ATOMIC_RELAXED);
      __sync_synchronize(); // Full memory barrier
      wake_up_all();
    }
    mempool_wfi();
    if (core_id == 0) {
      set_wake_up_stride(1U);
      set_wake_up_offset(0U);
      printf("Cores woken up with stride 4 over the whole cluster \n");
    }
  }
  // Stops the remaining cores
  if ((num_cores - 1) == __atomic_fetch_add(&sleep2, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(&sleep2, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  mempool_wfi();

  /* WAKE-UP GROUP TEST */

  if (core_id < NUM_CORES_PER_GROUP) {
    if (core_id % 2 == 0) {
      if (core_id == 0) {
        set_wake_up_stride(2U);
        set_wake_up_offset(0U);
      }
      if ((NUM_CORES_PER_GROUP / 2 - 1) ==
          __atomic_fetch_add(&sleep1, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep1, 0, __ATOMIC_RELAXED);
        __sync_synchronize(); // Full memory barrier
        wake_up_group(0b0001);
      }
      mempool_wfi();
      if (core_id == 0) {
        set_wake_up_stride(1U);
        set_wake_up_offset(0U);
        printf("Cores woken up with stride 2 over a group \n");
      }
    }
  }
  // Stops the remaining cores
  if ((num_cores - 1) == __atomic_fetch_add(&sleep2, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(&sleep2, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  mempool_wfi();

  /* WAKE-UP TILE TEST */

  if (core_id < NUM_CORES_PER_TILE) {
    if (core_id % 2 == 0) {
      if (core_id == 0) {
        set_wake_up_stride(2U);
        set_wake_up_offset(0U);
      }
      if ((NUM_CORES_PER_TILE / 2 - 1) ==
          __atomic_fetch_add(&sleep1, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep1, 0, __ATOMIC_RELAXED);
        wake_up_tile(0, 1U);
      }
      mempool_wfi();
    }
    if (core_id == 0) {
      set_wake_up_stride(1U);
      set_wake_up_offset(0U);
      printf("Cores woken up with stride 2 over a tile \n");
    }
  }
  // Stops the remaining cores
  if ((num_cores - 1) == __atomic_fetch_add(&sleep2, 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(&sleep2, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  mempool_wfi();

  return 0;
}
