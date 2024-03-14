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
uint32_t volatile l2_var __attribute__((section(".l2")));

int main() {
  // uint32_t num_cores_per_group = NUM_CORES / NUM_GROUPS;
  uint32_t core_id = mempool_get_core_id();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    // Put golden value in L2 memory
    uint32_t const golden = 1234;
    uint32_t const overwrite = 5678;
    uint32_t read_fence = 0;
    uint32_t read_no_fence = 0;
    l2_var = golden;
    // Program DMA to create pressure on the read channel of the L2 and wait a
    // few cycles
    dma_memcpy_nonblocking(l1_data, l2_data, SIZE * sizeof(uint32_t));
    mempool_wait(32);
    // Trigger an inconsistency by trying to have a write overtake a read
    __asm__ volatile(
        ".balign 16 \n\t"
        // Read from L2
        "lw %[read_no_fence], (%[l2_var]) \n\t"
        // Write to L2
        "sw %[overwrite], (%[l2_var]) \n\t"
        : [read_no_fence] "+&r"(read_no_fence)              // Outputs
        : [overwrite] "r"(overwrite), [l2_var] "r"(&l2_var) // Inputs
        : "memory");                                        // Clobber
    printf("read_no_fence %d\n", read_no_fence);
    // Reset the memory and wait
    l2_var = golden;
    dma_wait();

    // Again but with a fence
    // Program DMA to create pressure on the read channel of the L2
    dma_memcpy_nonblocking(l1_data, l2_data, SIZE * sizeof(uint32_t));
    mempool_wait(32);
    // Trigger an inconsistency by trying to have a write overtake a read
    __asm__ volatile(
        ".balign 16 \n\t"
        // Read from L2
        "lw %[read_fence], (%[l2_var]) \n\t"
        // Fence
        "fence \n\t"
        // Write to L2
        "sw %[overwrite], (%[l2_var]) \n\t"
        : [read_fence] "+&r"(read_fence)                    // Outputs
        : [overwrite] "r"(overwrite), [l2_var] "r"(&l2_var) // Inputs
        : "memory");                                        // Clobber
    printf("read_fence %d\n", read_fence);
    // Reset the memory and wait
    dma_wait();

    // Check
    if (read_no_fence == golden) {
      printf("Test did not trigger inconsistency\n");
    }
    if (read_fence != golden) {
      printf("Fence failde!\n");
      return 1;
    }
  } else {
    mempool_wfi();
  }

  return 0;
}
