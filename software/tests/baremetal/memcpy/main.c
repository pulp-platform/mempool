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

// Size in words
#ifndef SIZE
#define SIZE (8192)
#endif

#define DMA_ADDRESS (0x40010000)
//#define VERIFY

// Assume banking factor of 4
int32_t l1_data[SIZE] __attribute__((section(".l1_prio")))
__attribute__((aligned(NUM_CORES * 4 * 4)));
int32_t l2_data_move_out[SIZE] __attribute__((section(".l2_prio")))
__attribute__((aligned(16 * 512)));

dump(addr, 0);
dump(end, 3);
dump(dma, 7);

void dump_data(volatile uint32_t *addr, uint32_t num_words) {
  for (uint32_t i = 0; i < num_words; ++i) {
    dump_dma((uint32_t)addr[i]);
  }
}

void verify_dma_single_core(int32_t *addr, uint32_t num_words, int32_t *golden,
                            int32_t error) {
  volatile int32_t *a = (volatile int32_t *)addr;
  for (uint32_t i = 0; i < num_words; ++i) {
    if (a[i] != *golden) {
      printf("The %dth value is %d, the golden is %d \n", i, a[i], *golden);
      error = error + 1;
    }
    golden += 1;
  }
}

void verify_dma_parallel(int32_t *addr, uint32_t num_words, uint32_t id,
                         uint32_t num_threads, int32_t *golden, int32_t error) {
  volatile int32_t *a = (volatile int32_t *)addr;
  volatile int32_t *b = (volatile int32_t *)golden;
  uint32_t size = num_words / num_threads;
  uint32_t start = id * size;
  uint32_t end = start + size;
  for (uint32_t i = start; i < end; ++i) {
    if (a[i] != b[i]) {
      error = error + 1;
      break;
    }
  }
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  int32_t error = 0;

  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    // Benchmark
    dump_addr((uint32_t)l2_data);
    dump_addr((uint32_t)l2_data_move_out);
    dump_addr((uint32_t)l1_data);

    // Copy in
    uint32_t time = mempool_get_timer();
    dma_memcpy_blocking(l1_data, l2_data, SIZE * sizeof(int32_t));
    time = mempool_get_timer() - time;
    dump_end(time);
  }

  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Copy out
    uint32_t time = mempool_get_timer();
    dma_memcpy_blocking(l2_data_move_out, l1_data, SIZE * sizeof(int32_t));
    time = mempool_get_timer() - time;
    dump_end(time);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);

// Verify
#ifdef VERIFY
  if (core_id == 0) {
    verify_dma_single_core(l2_data_move_out, SIZE, l2_data, error);
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#endif

  return error;
}
