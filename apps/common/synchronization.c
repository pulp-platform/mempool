// Copyright 2020 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Samuel Riedel, ETH Zurich

static inline unsigned amo_add(void volatile *const address, unsigned value);

#include <stdbool.h>
#include <stdint.h>

#include "runtime.h"
#include "synchronization.h"

uint32_t volatile barrier __attribute__((section(".l1")));
uint32_t volatile barrier_iteration __attribute__((section(".l1")));
uint32_t volatile barrier_init __attribute__((section(".l2"))) = 0;

void mempool_barrier_init(uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    barrier = 0;
    barrier_iteration = 0;
    barrier_init = 1;
  } else {
    while (!barrier_init)
      mempool_wait(2 * num_cores);
  }
}

void mempool_barrier_init_sleep(uint32_t core_id, uint32_t num_cores) {
  if (core_id == 0) {
    // Give other cores time to go to sleep
    mempool_wait(4 * num_cores);
    barrier = 0;
    barrier_iteration = 0;
    barrier_init = 1;
    wake_up((uint32_t)-1);
  } else {
    mempool_wfi();
  }
}

void mempool_barrier(uint32_t num_cores, uint32_t cycles) {
  // Remember previous iteration
  uint32_t iteration_old = barrier_iteration;

  // Increment the barrier counter
  if ((num_cores - 1) ==
      amo_add(&barrier, 1)) { /* if __atomic_fetch_add built-in not defined */
    //__atomic_fetch_add(&barrier, 1, __ATOMIC_SEQ_CST)) {
    // We are the last one to reach the barrier --> reset barrier and increment
    // barrier_iteration
    barrier = 0;
    //__atomic_fetch_add(&barrier_iteration, 1, __ATOMIC_SEQ_CST);
    amo_add(&barrier_iteration, 1);
  } else {
    // Some threads have not reached the barrier --> Let's wait
    while (iteration_old == barrier_iteration)
      mempool_wait(cycles);
  }
}

/**

 * Expose the atomic add instruction.
 *
 * @param   address     A pointer to an address on L2 memory to store the value.
 * @param   value       Value to add to the specified memory location.
 *
 * @return  Value previously stored in memory.
 */
static inline unsigned amo_add(void volatile *const address, unsigned value) {
  unsigned ret;
  __asm__ __volatile__("" : : : "memory");
  asm volatile("amoadd.w  %0, %1, (%2)" : "=r"(ret) : "r"(value), "r"(address));
  __asm__ __volatile__("" : : : "memory");
  return ret;
}
