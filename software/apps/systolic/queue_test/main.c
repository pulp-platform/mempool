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
#include "systolic/queue.h"

extern int32_t __heap_start, __heap_end;

queue_t *queue = 0;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id, num_cores);

  // Setup
  if (core_id == 0) {
    printf("Initialize\n");

    // Initialize malloc
    uint32_t heap_size = (uint32_t)(&__heap_end - &__heap_start);
    alloc_init(get_alloc_l1(), &__heap_start, heap_size);

    // Create queue
    queue_create(&queue, 8);
  }

  // Wait for all cores
  mempool_barrier(num_cores, num_cores * 4);

  // Producer
  if (core_id == 0) {
    int32_t data[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};
    for (uint32_t i = 0; i < 16; ++i) {
      while (queue_push(queue, &data[i])) {
        mempool_wait(5);
      }
    }
  }

  // Consumer
  if (core_id == 1) {
    int32_t read_data;
    for (uint32_t i = 0; i < 16; ++i) {
      while (queue_pop(queue, &read_data)) {
        mempool_wait(5);
      }
      printf("Received: %d\n", read_data);
    }
  }

  // wait until all cores have finished
  mempool_barrier(num_cores, num_cores * 4);
  return 0;
}
