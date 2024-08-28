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
#define SIZE (12288)

uint32_t l1_data[SIZE] __attribute__((section(".l1_prio")));
uint32_t volatile l2_var[2] __attribute__((section(".l2")));
uint32_t volatile error_no_fence __attribute__((section(".l1")));
uint32_t volatile error_fence __attribute__((section(".l1")));

dump(no_fence, 10);
dump(fence, 11);

// Simple Litmus test
//
// location l0 and l1 are initialized to `golden` and after reading overwritten
// with `overwrite`
//
// b = `overwrite`
// Core 0    | Core 1
// lw a (l1) | lw a (l0)
// fence     | fence
// sw b (l0) | sw b (l1)
//
// With the fence, at least one core must have a=`golden`, but it is possible
// that one core has a=`overwrite`. Without a fence, it is allowed that both
// cores end up with a=`overwrite`. This test first executes without a fence to
// trigger this "inconsistency" and reports on whether the scenario is possible
// to validate that the test could actually fail. The second iteration runs with
// a fence and checks for the one prohibited outcome (both cores have
// a=`overwrite`). To maximize the chance of writes overtaking reads, we use the
// DMA to stress the read channel into the L2 memory.
//
// Expected outcome:
// Without a fence:
// [DUMP] Core 0: 0x00a = 5678  // a = `overwrite`. Inconsistency triggered
// [DUMP] Core 1: 0x00a = 5678  // a = `overwrite`. Inconsistency triggered
// With the fence
// [DUMP] Core 0: 0x00b = 1234 // a = `golden`.
// [DUMP] Core 1: 0x00b = 1234 // a = `golden`.
// (One of them being 'overwrite' would also be allowed)

int main() {
  // uint32_t num_cores_per_group = NUM_CORES / NUM_GROUPS;
  uint32_t core_id = mempool_get_core_id();
  uint32_t cluster_id = mempool_get_cluster_id();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Only use the first two cores
  if (core_id <= 1) {
    // Initialize the error variables
    error_no_fence = 1;
    error_fence = 1;
    // Put golden value in L2 memory
    uint32_t const golden = 1234;
    uint32_t const overwrite = 5678;
    uint32_t read_fence = 0;
    uint32_t read_no_fence = 0;
    uint32_t other_core_id = core_id == 0 ? 1 : 0;
    l2_var[core_id] = golden;
    // Program DMA to create pressure on the read channel of the L2 and wait a
    // few cycles
    if (core_id == 0) {
      dma_memcpy_nonblocking(cluster_id, l1_data, l2_data,
                             SIZE * sizeof(uint32_t));
      wake_up_tile(0, 1);
    }
    // Trigger an inconsistency by trying to have a write overtake a read
    __asm__ volatile(
        ".balign 16 \n\t"
        // Sleep to synchronize
        "wfi \n\t"
        // Read from L2
        "lw %[read_no_fence], (%[l2_var_other]) \n\t"
        // Write to L2
        "sw %[overwrite], (%[l2_var_ours]) \n\t"
        : [read_no_fence] "+&r"(read_no_fence) // Outputs
        : [overwrite] "r"(overwrite), [l2_var_ours] "r"(&l2_var[core_id]),
          [l2_var_other] "r"(&l2_var[other_core_id]) // Inputs
        : "memory");                                 // Clobber
    dump_no_fence(read_no_fence);
    // Reset the memory and wait
    l2_var[core_id] = golden;
    // Run the check
    __atomic_fetch_and(&error_no_fence, read_no_fence != golden,
                       __ATOMIC_RELAXED);
    dma_wait(cluster_id);

    // Again but with a fence
    // Program DMA to create pressure on the read channel of the L2
    if (core_id == 0) {
      dma_memcpy_nonblocking(cluster_id, l1_data, l2_data,
                             SIZE * sizeof(uint32_t));
      wake_up_tile(0, 1);
    }
    // Trigger an inconsistency by trying to have a write overtake a read
    __asm__ volatile(
        ".balign 16 \n\t"
        // Sleep to synchronize
        "wfi \n\t"
        // Read from L2
        "lw %[read_fence], (%[l2_var_other]) \n\t"
        // Fence
        "fence \n\t"
        // Write to L2
        "sw %[overwrite], (%[l2_var_ours]) \n\t"
        : [read_fence] "+&r"(read_fence) // Outputs
        : [overwrite] "r"(overwrite), [l2_var_ours] "r"(&l2_var[core_id]),
          [l2_var_other] "r"(&l2_var[other_core_id]) // Inputs
        : "memory");                                 // Clobber
    dump_fence(read_fence);
    // Check and wait
    __atomic_fetch_and(&error_fence, read_fence != golden, __ATOMIC_RELAXED);
    dma_wait(cluster_id);

    // Barrier between core 0 and 1
    if (core_id == 0) {
      wake_up(1);
      mempool_wfi();
    } else {
      mempool_wfi();
      wake_up(0);
    }

    // Check only from core 0
    if (core_id == 0) {
      if (!error_no_fence) {
        printf("Test did not trigger inconsistency\n");
      }
      if (error_fence) {
        printf("Fence failed!\n");
        return 1;
      }
    } else {
      // Core 1 can go to sleep
      mempool_wfi();
    }
  } else {
    while (1) {
      mempool_wfi();
    }
  }
  return 0;
}
