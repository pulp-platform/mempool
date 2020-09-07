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

void mempool_barrier(uint32_t core_id, uint32_t num_cores, uint32_t cycles) {
  // Remember previous iteration
  uint32_t iteration_old = barrier_iteration;
  // Increment the barrier counter
  if ((mempool_get_core_count() - 1) ==
      __atomic_fetch_add(&barrier, 1, __ATOMIC_SEQ_CST)) {
    // We are the last one to reach the barrier --> reset barrier and increment
    // barrier_iteration
    barrier = 0;
    __atomic_fetch_add(&barrier_iteration, 1, __ATOMIC_SEQ_CST);
  } else {
    // Some threads have not reached the barrier --> Let's wait
    while (iteration_old == barrier_iteration)
      mempool_wait(cycles);
  }
}
