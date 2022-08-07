// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "kernel/synth.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define UNROLL (4)
#define N (NUM_CORES * UNROLL)

int32_t block_a[N] __attribute__((aligned(NUM_CORES * 4), section(".l1")));

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
  mempool_barrier(num_cores);
  power_profile(block_a);
  mempool_barrier(num_cores);
  power_profile(block_a);

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return 0;
}
