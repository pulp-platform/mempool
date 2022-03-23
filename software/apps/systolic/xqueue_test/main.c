// Copyright 2021 ETH Zurich and University of Bologna.
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

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

int32_t *queue = 0;

int32_t producer_check, consumer_check, dummy_check;

// queue push
static inline int32_t queue_push(void *const queue, int32_t data) {
  int32_t ret;
  asm volatile ("q.push.w %0, %1, (%2)" : "=r"(ret) : "r"(data), "r"(queue));
  return ret;
}

// queue pop
inline int32_t queue_pop(void *const queue) {
  int32_t ret;
  asm volatile ("q.pop.w %0, 0(%1)" : "=r"(ret) : "r"(queue));
  return ret;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  extern int32_t __seq_start;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id, num_cores);

  // Setup
  if (core_id == 0) {
    printf("Initialize\n");
    queue = &__seq_start;
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Producer
  if (core_id == 0) {
    int32_t data[16] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16};
    int32_t check = 0;
    int32_t resp;
    int32_t dummy = 0;
    for (uint32_t i = 0; i < 16; ++i) {
      resp = queue_push(queue, data[i]);
      dummy += resp;
    }
    for (uint32_t i = 0; i < 16; ++i) {
      resp = queue_push(queue, data[i]);
      dummy += resp;
      check += data[i];
    }
    producer_check = check;
    dummy_check = dummy;
  }

  // Consumer
  if (core_id == 1) {
    int32_t read_data;
    int32_t check = 0;
    for (uint32_t i = 0; i < 16; ++i) {
      read_data = queue_pop(queue);
      printf("Rx: %d\n", read_data);
    }
    printf("Burst Test\n");
    for (uint32_t i = 0; i < 16; ++i) {
      read_data = queue_pop(queue);
      check += read_data;
    }
    consumer_check = check;
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Print both checks
  if (core_id == 0) {
    printf("Check: %d/%d/%d\n", producer_check, consumer_check, dummy_check);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
