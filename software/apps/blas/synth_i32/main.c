// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
// Author: Yichao Zhang,  ETH Zurich

#include <stdint.h>
#include <string.h>

#include "baremetal/mempool_synth_i32p.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// Macros
#define UNROLL (BANKING_FACTOR)
#define N (NUM_CORES * BANKING_FACTOR)
#define TARGET_MEMPOOL (1)
#define TARGET_TERAPOOL (0)

// Globals
int32_t block_a[N]
    __attribute__((aligned(NUM_CORES * BANKING_FACTOR), section(".l1")));

/* Main */

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  for (int i = (int)core_id * UNROLL; i < N; i += (int)(num_cores * UNROLL)) {
    // UNROLL
    block_a[i + 0] = -1111608459 + i * (52918781);
    block_a[i + 1] = -192269334 + i * (942963224);
    block_a[i + 2] = 600576702 + i * (-1245786405);
    block_a[i + 3] = 132428405 + i * (232792075);
  }

// Barrier
#if (TARGET_MEMPOOL == 1)
  mempool_barrier(num_cores);
  power_profile_mempool(block_a, core_id);
  mempool_barrier(num_cores);
  power_profile_mempool(block_a, core_id);

#elif (TARGET_TERAPOOL == 1)
  // normal instr testing
  mempool_barrier(num_cores);
  power_profile_terapool(block_a, core_id);

  // Remote tile lw testing
  // Don't use core_0 to avoid lsu conflict with barrier
  mempool_barrier(num_cores);
  uint32_t tile_id = (core_id / NUM_CORES_PER_TILE) % NUM_TILES_PER_SUB_GROUP;
  uint32_t sub_group_id =
      (core_id / NUM_CORES_PER_SUB_GROUP) % NUM_SUB_GROUPS_PER_GROUP;
  uint32_t group_id = (core_id / NUM_CORES_PER_GROUP) % NUM_GROUPS;
  uint32_t number_banks_per_sub_group =
      BANKING_FACTOR * NUM_CORES_PER_SUB_GROUP;
  uint32_t number_banks_per_group = BANKING_FACTOR * NUM_CORES_PER_GROUP;
  uint32_t remote_tile =
      (core_id * BANKING_FACTOR + NUM_BANKS_PER_TILE) -
      (tile_id / (NUM_TILES_PER_SUB_GROUP - 1)) * number_banks_per_sub_group;
  uint32_t remote_sub_group =
      (core_id * BANKING_FACTOR +
       ((core_id % 8) + 1) * number_banks_per_sub_group) -
      ((sub_group_id + (core_id % 8)) / (NUM_SUB_GROUPS_PER_GROUP - 1)) *
          number_banks_per_group;
  uint32_t remote_group = (core_id * BANKING_FACTOR +
                           ((core_id % 8) + 1) * number_banks_per_group) -
                          ((group_id + (core_id % 8)) / (NUM_GROUPS - 1)) *
                              NUM_CORES * BANKING_FACTOR;

  // Only use one core to avoid stalls caused by conflict
  if ((core_id % 8) == 6) {
    power_profile_terapool_lw_rtile(block_a, remote_tile);
  } else {
    mempool_wait(500);
  }

  // Remote sub-group/group lw testing
  mempool_barrier(num_cores);
  if ((core_id % 8) < 3) {
    power_profile_terapool_lw_rgrup(block_a, remote_sub_group, remote_group);
  } else {
    mempool_wait(2000);
  }

#else
  if (core_id == 0) {
    printf("ERROR: Please specify TARGET for simulation\n");
  }
#endif

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return 0;
}
