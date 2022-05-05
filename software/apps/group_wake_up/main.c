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

uint32_t volatile sleep __attribute__((section(".l1")));
//dump(current_sleep,   1);

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id);
  if(core_id == 0){
    sleep = 0;
  }
  mempool_barrier(num_cores);

  if (core_id < 64) {
    if (63 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      printf("Hello, I'm core %d and I woke up the first group!\n", core_id);
      wake_up_group(0b0001);
    }
    mempool_wfi(); //clear wake-up trigger
  }
  mempool_barrier(num_cores);

  if (core_id < 128) {
    if (127 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      printf("Hello, I'm core %d and I woke up the first and the second group!\n", core_id);
      wake_up_group(0b0011);
    }
    mempool_wfi(); //clear wake-up trigger
  }
  mempool_barrier(num_cores);

  if (core_id < 192) {
    if (191 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      printf("Hello, I'm core %d and I woke up the first, the second and the third group!\n", core_id);
      wake_up_group(0b0111);
    }
    mempool_wfi(); //clear wake-up trigger
  }
  mempool_barrier(num_cores);

  if (core_id < 256) {
    if (255 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      printf("Hello, I'm core %d and I woke up all the groups!\n", core_id);
      //wake_up_all_group();
      wake_up_group(0b1111);
    }
    mempool_wfi(); //clear wake-up trigger
  }
  //mempool_barrier(num_cores);

  return 0;

}
