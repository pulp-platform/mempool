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

uint32_t volatile sleep __attribute__((section(".l1")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id);
  if(core_id == 0){
    sleep = 0;
  }
  mempool_barrier(num_cores);

  if (core_id > 19 && core_id < 24) {
    if (3 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
      __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
      __sync_synchronize();
      printf("Hello, I'm core %d and I woke-up the sixth tile in group %d!\n",
             core_id, 0);
      wake_up_tile(0, (uint32_t)(1 << 5));
    }
    mempool_wfi(); // clear wake-up trigger
  }
  mempool_barrier(num_cores);

  for (uint32_t i = 0; i < 16; i++) {
    if (core_id < (i + 1) * 4) {
      if ((i + 1) * 4 - 1 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
        __sync_synchronize();
        printf("Hello, I'm core %d and I woke-up %d tiles in group %d!\n",
               core_id, i + 1, 0);
        wake_up_tile(0, (uint32_t)(1 << (i + 1)) - 1);
      }
      mempool_wfi(); //clear wake-up trigger
    }
    mempool_barrier(num_cores);
  }

  mempool_barrier(num_cores);

  for(uint32_t i = 0; i<16; i++) {
    if(core_id < 64+(i+1)*4 && core_id > 63 ) {
      if ((i+1)*4-1 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
        __sync_synchronize();
        printf("Hello, I'm core %d and I woke-up %d tiles in group %d!\n",
               core_id, i + 1, 1);
        wake_up_tile(1, (uint32_t)(1 << (i + 1)) - 1);
      }
      mempool_wfi(); //clear wake-up trigger
    }
    mempool_barrier(num_cores);
  }

  mempool_barrier(num_cores);

  for(uint32_t i = 0; i<16; i++) {
    if(core_id < 128+(i+1)*4 && core_id > 127 ) {
      if ((i+1)*4-1 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
        __sync_synchronize();
        printf("Hello, I'm core %d and I woke-up %d tiles in group %d!\n",
               core_id, i + 1, 2);
        wake_up_tile(2, (uint32_t)(1 << (i + 1)) - 1);
      }
      mempool_wfi(); //clear wake-up trigger
    }
    mempool_barrier(num_cores);
  }

  for (uint32_t i = 0; i < 16; i++) {
    if (core_id < 192 + (i + 1) * 4 && core_id > 191) {
      if ((i + 1) * 4 - 1 == __atomic_fetch_add(&sleep, 1, __ATOMIC_RELAXED)) {
        __atomic_store_n(&sleep, 0, __ATOMIC_RELAXED);
        __sync_synchronize();
        printf("Hello, I'm core %d and I woke-up %d tiles in group %d!\n",
               core_id, i + 1, 3);
        wake_up_tile(3, (uint32_t)(1 << (i + 1)) - 1);
      }
      mempool_wfi(); //clear wake-up trigger
    }
    mempool_barrier(num_cores);
  }

  return 0;

}
