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

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialization
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  if (core_id == 0) {

    // --------------------------------------------
    // Verify DAS partitions
    // --------------------------------------------
    printf("Verify DAS partitions\n\n");

    uint32_t num_tiles_per_partition = 4;
    uint32_t array_size =
        2 * num_tiles_per_partition * BANKING_FACTOR * NUM_CORES_PER_TILE;

    // 1. Init dynamic heap allocator
    mempool_dynamic_heap_alloc_init(core_id);

    // 2. Set which partition write to.
    for (uint32_t part_id = 0; part_id < NUM_DAS_PARTITIONS; part_id++) {
      // 3. Get the allocator
      alloc_t *dynamic_heap_alloc = get_dynamic_heap_alloc();
      alloc_dump(dynamic_heap_alloc);

      // 4. Allocate memory
      uint32_t *array = (uint32_t *)partition_malloc(
          dynamic_heap_alloc, array_size * sizeof(uint32_t));
      printf("start_addr at 0x%8x\n", array);

      // 5. Config the hardware registers
      das_config(part_id, num_tiles_per_partition, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // 6. Move data
      for (uint32_t i = 0; i < array_size; i++) {
        array[i] = i;
      }
      // 7. Change addressing scheme (to fully interleaved)
      das_config(part_id, NUM_TILES, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // 8. check
      for (uint32_t i = 0; i < array_size; i++) {
        uint32_t *fetch_address =
            &array[0] +
            (i %
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) +
            (i /
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) *
                NUM_BANKS;
        if (i != *fetch_address) {
          printf("%4d != %4d at address %8X.\n", i, *fetch_address,
                 fetch_address);
          return 1;
        }
      }
      // 9. Free array
      partition_free(dynamic_heap_alloc, array);
      printf("SUCCESS on partition %d \n\n", part_id);
    }

    // --------------------------------------------
    // Verify DAS partitions with misalignment
    // --------------------------------------------
    printf("Verify DAS partitions with misalignemnt\n\n");

    // 2. Set which partition write to.
    for (uint32_t part_id = 0; part_id < NUM_DAS_PARTITIONS; part_id++) {
      // 3. Get the allocator
      alloc_t *dynamic_heap_alloc = get_dynamic_heap_alloc();
      alloc_dump(dynamic_heap_alloc);

      // 4.0 inject misalignment
      uint32_t offset = 32 * (1 + part_id);
      uint32_t *misalign = (uint32_t *)partition_malloc(
          dynamic_heap_alloc, (2 * NUM_BANKS + offset) * sizeof(uint32_t));
      printf("Inject misalignment at 0x%8x with size 0x%8x in byte\n", misalign,
             offset * part_id);

      // 4. Allocate memory
      uint32_t *array = (uint32_t *)partition_malloc(
          dynamic_heap_alloc, array_size * sizeof(uint32_t));
      printf("Aligned start_addr at 0x%8x\n", array);

      // 5. Config the hardware registers
      das_config(part_id, num_tiles_per_partition, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // 6. Move data
      for (uint32_t i = 0; i < array_size; i++) {
        array[i] = i;
      }
      // 7. Change addressing scheme (to fully interleaved)
      das_config(part_id, NUM_TILES, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // 8. check
      for (uint32_t i = 0; i < array_size; i++) {
        uint32_t *fetch_address =
            &array[0] +
            (i %
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) +
            (i /
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) *
                NUM_BANKS;
        if (i != *fetch_address) {
          printf("%4d != %4d at address %8X.\n", i, *fetch_address,
                 fetch_address);
          return 1;
        }
      }
      // 9. Free array
      partition_free(dynamic_heap_alloc, array);
      partition_free(dynamic_heap_alloc, misalign);
      printf("SUCCESS on partition %d \n\n", part_id);
    }

    // --------------------------------------------
    // Verify DAS per Tile groups
    // --------------------------------------------
    printf("Verify DAS per Tile-groups\n\n");

    // 2. Set which partition write to.
    uint32_t part_id = 0;
    for (num_tiles_per_partition = 1; num_tiles_per_partition < NUM_TILES;
         num_tiles_per_partition *= 2) {
      array_size =
          2 * num_tiles_per_partition * BANKING_FACTOR * NUM_CORES_PER_TILE;
      // 3. Get the allocator
      alloc_t *dynamic_heap_alloc = get_dynamic_heap_alloc();
      alloc_dump(dynamic_heap_alloc);
      // 4. Allocate memory
      uint32_t *array = (uint32_t *)partition_malloc(
          dynamic_heap_alloc, array_size * sizeof(uint32_t));
      // 5. Config the hardware registers
      das_config(part_id, num_tiles_per_partition, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // 6. Move data
      for (uint32_t i = 0; i < array_size; i++) {
        array[i] = i;
      }
      // 7. Change addressing scheme (to fully interleaved)
      das_config(part_id, NUM_TILES, (uint32_t)(array),
                 array_size * sizeof(uint32_t));
      // partition_config(part_id, NUM_TILES);
      // 8. check
      for (uint32_t i = 0; i < array_size; i++) {
        uint32_t *fetch_address =
            &array[0] +
            (i %
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) +
            (i /
             (num_tiles_per_partition * NUM_CORES_PER_TILE * BANKING_FACTOR)) *
                NUM_BANKS;
        if (i != *fetch_address) {
          printf("%4d != %4d at address %8X.\n", i, *fetch_address,
                 fetch_address);
          return 1;
        }
      }
      // 9. Free array
      partition_free(dynamic_heap_alloc, array);
      printf("SUCCESS for groups of %d tiles over the partition \n\n",
             num_tiles_per_partition);
    }

    printf("All correct!\n");
  }

  mempool_barrier(num_cores);
  return 0;
}
