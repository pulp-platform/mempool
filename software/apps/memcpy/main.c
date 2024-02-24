// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "mempool_dma_frontend.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#ifndef UNROLL
#define UNROLL 1
#endif
#ifndef GROUP
#define GROUP 1
#endif

#define DMA_ADDRESS (0x40010000)

// Size in words
#ifndef SIZE
#define SIZE ((NUM_CORES) * (NUM_CORES)*2)
#endif
// Assume banking factor of 4

uint32_t l1_data[SIZE] __attribute__((section(".l1_prio")))
__attribute__((aligned(NUM_CORES * 4 * 4)));

dump(addr, 0);
dump(start, 2);
dump(end, 3);
dump(dma, 7);

void dump_data(volatile uint32_t *addr, uint32_t num_words) {
  for (uint32_t i = 0; i < num_words; ++i) {
    dump_dma((uint32_t)addr[i]);
  }
}

uint32_t verify_dma(uint32_t *addr, uint32_t num_words, uint32_t golden) {
  volatile uint32_t *a = (volatile uint32_t *)addr;
  for (uint32_t i = 0; i < num_words; ++i) {
    if (a[i] != golden) {
      return i + 1;
    }
    golden += 4;
  }
  return 0;
}

int main() {
  // uint32_t num_cores_per_group = NUM_CORES / NUM_GROUPS;
  uint32_t core_id = mempool_get_core_id();
  // uint32_t group_id = core_id / num_cores_per_group;
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    // Benchmark
    dump_addr((uint32_t)l2_data);
    dump_addr((uint32_t)l1_data);
    // Copy in
    // mempool_start_benchmark();
    uint32_t time = mempool_get_timer();
    dma_memcpy_nonblocking(l1_data, l2_data, SIZE * sizeof(uint32_t));
    do {
      mempool_wait(512);
    } while (!dma_done());
    time = mempool_get_timer() - time;
    dump_end(time);
    printf("Core %3d Copy in is done\n", core_id);
    // mempool_stop_benchmark();

    // Copy out
    // printf("Core %3d Now we want to start copy out\n", core_id);
    // // mempool_start_benchmark();
    // time = mempool_get_timer();
    // dump_start(time);
    // dma_memcpy_nonblocking(l2_data, l1_data, SIZE * sizeof(uint32_t));
    // do {
    //   mempool_wait(512);
    // } while (!dma_done());
    // time = mempool_get_timer() - time;
    // dump_end(time);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return 0;
}
