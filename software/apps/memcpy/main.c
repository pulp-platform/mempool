// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "mempool_dma_frontend.h"

#ifndef UNROLL
#define UNROLL 1
#endif
#ifndef GROUP
#define GROUP 1
#endif

#define DMA_ADDRESS (0x40010000)

int8_t ro_data[0xC000] __attribute__((section(".rodata")))
__attribute__((aligned(0x1000)));

#define SIZE (1024 * 2)
int32_t volatile dst_a[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(1024)));
int32_t volatile dst_b[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(1024)));
int32_t volatile dst_c[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(1024)));
int32_t volatile dst_d[SIZE] __attribute__((section(".l1")))
__attribute__((aligned(1024)));

int volatile error __attribute__((section(".l1")));

dump(start, 2);
dump(end, 3);

void *mempool_memcpy(void *destination, const void *source, size_t num) {
  if ((((size_t)destination | (size_t)source | num) &
       (8 * sizeof(uint32_t) - 1)) == 0) {
    // Aligned to 8 words
    uint32_t *d = (uint32_t *)destination;
    const uint32_t *s = (uint32_t *)source;
    while (d < (uint32_t *)(destination + num)) {
      uint32_t tmp_0 = *s++;
      uint32_t tmp_1 = *s++;
      uint32_t tmp_2 = *s++;
      uint32_t tmp_3 = *s++;
      uint32_t tmp_4 = *s++;
      uint32_t tmp_5 = *s++;
      uint32_t tmp_6 = *s++;
      uint32_t tmp_7 = *s++;
      *d++ = tmp_0;
      *d++ = tmp_1;
      *d++ = tmp_2;
      *d++ = tmp_3;
      *d++ = tmp_4;
      *d++ = tmp_5;
      *d++ = tmp_6;
      *d++ = tmp_7;
    }
  } else {
    return memcpy(destination, source, num);
  }

  return destination;
}

void *parallel_memcpy(void *destination, const void *source, size_t num_bytes,
                      uint32_t core_id, uint32_t num_cores) {
  // Assume all cores work together on the memcopy
  uint32_t group = GROUP;
  uint32_t chunks = num_bytes / (num_cores / group);
  uint32_t *d = (uint32_t *)(destination + (core_id / group) * chunks);
  const uint32_t *s = (uint32_t *)(source + (core_id / group) * chunks);
  // Offset within the group
  d += core_id % group;
  s += core_id % group;
  // Only run if the data is nicely aligned
  if ((((size_t)destination | (size_t)source | num_bytes) &
       (num_cores * sizeof(uint32_t) - 1)) == 0) {
    while (d < (uint32_t *)(destination + (core_id / group + 1) * chunks)) {
#if UNROLL == 2
      uint32_t tmp_0 = *s;
      s += group;
      uint32_t tmp_1 = *s;
      s += group;
      *d = tmp_0;
      d += group;
      *d = tmp_1;
      d += group;
#elif UNROLL == 4
      uint32_t tmp_0 = *s;
      s += group;
      uint32_t tmp_1 = *s;
      s += group;
      uint32_t tmp_2 = *s;
      s += group;
      uint32_t tmp_3 = *s;
      s += group;
      *d = tmp_0;
      d += group;
      *d = tmp_1;
      d += group;
      *d = tmp_2;
      d += group;
      *d = tmp_3;
      d += group;
#else
      uint32_t tmp_0 = *s;
      s += group;
      *d = tmp_0;
      d += group;
#endif
    }
  } else {
    return NULL;
  }
  return destination;
}

void *dma_memcpy(void *destination, const void *source, size_t num) {
  *(volatile uint32_t *)(DMA_ADDRESS + MEMPOOL_DMA_FRONTEND_DST_ADDR_REG_OFFSET) = (uint32_t) destination;
  *(volatile uint32_t *)(DMA_ADDRESS + MEMPOOL_DMA_FRONTEND_SRC_ADDR_REG_OFFSET) = (uint32_t) source;
  *(volatile uint32_t *)(DMA_ADDRESS + MEMPOOL_DMA_FRONTEND_NUM_BYTES_REG_OFFSET) = (uint32_t) num;
  uint32_t id = *(volatile uint32_t *)(DMA_ADDRESS + MEMPOOL_DMA_FRONTEND_NEXT_ID_REG_OFFSET);
  return destination;
}

int main() {
  uint32_t num_cores_per_group = NUM_CORES / NUM_GROUPS;
  uint32_t core_id = mempool_get_core_id();
  uint32_t group_id = core_id / num_cores_per_group;
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
  }

  int32_t volatile *const src_a = (int32_t *)0x80002000;
  int32_t volatile *const src_b = (int32_t *)0x80004000;
  int32_t volatile *const src_c = (int32_t *)0x80008000;
  int32_t volatile *const src_d = (int32_t *)0x8000C000;

  // Benchmark
  mempool_start_benchmark();
  uint32_t time = mempool_get_timer();
  dump_start(time);
  if (core_id == 0)
  {
    dma_memcpy((void *)src_b, (const void *)src_a, SIZE * 4);
  }
  time = mempool_get_timer() - time;
  dump_end(time);
  mempool_stop_benchmark();

  __atomic_fetch_add(&error, (int)time, __ATOMIC_RELAXED);

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
