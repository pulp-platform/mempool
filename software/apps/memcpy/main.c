// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

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

#define SIZE (2 * 1024)
volatile uint32_t l2_data_a[SIZE] __attribute__((section(".l2")))
__attribute__((aligned(0x1000)));
volatile uint32_t l2_data_b[SIZE] __attribute__((section(".l2")))
__attribute__((aligned(0x1000)));

volatile uint32_t l1_data_a[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(0x1000)));
volatile uint32_t l1_data_b[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(0x1000)));

int volatile error __attribute__((section(".l1")));

dump(addr, 0);
dump(start, 2);
dump(end, 3);
dump(dma, 7);

void dump_data(volatile uint32_t *addr, uint32_t num_words) {
  for (uint32_t i = 0; i < num_words; ++i) {
    dump_dma((uint32_t)addr[i]);
  }
}

uint32_t verify_dma(volatile uint32_t *addr, uint32_t num_words,
                    uint32_t golden) {
  for (uint32_t i = 0; i < num_words; ++i) {
    if (addr[i] != golden) {
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
    error = 0;
    dump_addr((uint32_t)l2_data_a);
    dump_addr((uint32_t)l2_data_b);
    dump_addr((uint32_t)l1_data_a);
    dump_addr((uint32_t)l1_data_b);
  }

  // Init
  for (uint32_t i = core_id; i < SIZE; i += num_cores) {
    l2_data_a[i] = (uint32_t)l2_data_a + i * 4;
  }

  mempool_barrier(num_cores);

  // Benchmark
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t time = mempool_get_timer();
    dump_start(time);
    dma_memcpy_blocking(&l1_data_a[1], (const void *)l2_data_a + 8,
                        (1024 + 512) * 4);
    error +=
        verify_dma((void *)l1_data_a + 4, 1024 + 512, (uint32_t)l2_data_a + 8);
    dump_start(error);
    dump_start((uint32_t)l1_data_a);
    // dump_data(l1_data_a, SIZE);
    dma_memcpy_blocking((void *)l2_data_b, (const void *)l1_data_a + 4,
                        (1024 + 512) * 4);
    error += verify_dma((void *)l2_data_b, 1024 + 512, (uint32_t)l2_data_a + 8);
    dump_start(error);
    dump_start((uint32_t)l2_data_b);
    // dump_data(l2_data_b, SIZE);
    time = mempool_get_timer() - time;
    dump_end(time);
    mempool_stop_benchmark();
  }

  // __atomic_fetch_add(&error, (int)time, __ATOMIC_RELAXED);

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
