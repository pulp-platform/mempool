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

#define N 16

int32_t block_a[N] __attribute__((section(".l1_prio")));
int volatile error __attribute__((section(".l1")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    error = 0;
    for (int i = 0; i < N; ++i) {
      block_a[i] = 78459 + i;
    }
    power_profile(block_a);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);

  return error;
}
