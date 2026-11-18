// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Note: This test is only for Terapool dynamic heap allocation
// Author: Bowen Wang

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define NUM_TILES (NUM_CORES / NUM_CORES_PER_TILE)
#define ARRAY_SIZE (4096)

uint32_t array[ARRAY_SIZE]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id == 0) {

    // --------------------------------------------
    // Verify DAS partitions
    // --------------------------------------------
    printf("Verify DAS partitions\n\n");

    uint32_t num_tiles_per_partition = 64;
    uint32_t part_id = 0;

    uint32_t num_partitions = NUM_TILES / num_tiles_per_partition;
    uint32_t size_partition = ARRAY_SIZE / num_partitions;

    das_config(part_id, num_tiles_per_partition, (uint32_t)(array),
               ARRAY_SIZE * sizeof(uint32_t));
    for (uint32_t i = 0; i < ARRAY_SIZE; i++) {
      array[i] = i;
    }

    das_config(part_id, NUM_TILES, (uint32_t)(array),
               ARRAY_SIZE * sizeof(uint32_t));
    for (uint32_t j = 0; j < num_partitions; j++) {
      for (uint32_t i = 0; i < size_partition; i++) {

        uint32_t *fetch_address =
            &array[0] +
            j * (num_tiles_per_partition * NUM_CORES_PER_TILE *
                 BANKING_FACTOR) +
            (i %
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) +
            (i /
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) *
                NUM_BANKS;
        if (i + j * size_partition != *fetch_address) {
          printf("%4d != %4d at address %8X.\n", i + j * size_partition,
                 *fetch_address, fetch_address);
          return 1;
        }
      }
    }
    printf("SUCCESS on partition %d\n", part_id);
  }

  mempool_barrier(num_cores);
  return 0;
}
