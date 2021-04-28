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
#include "systolic/queue_multi.h"

queue_t *queue;

uint32_t producer_cnt;
uint32_t consumer_cnt;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  // Initialization
  mempool_init(core_id, num_cores);

  // Wait for all cores
  mempool_barrier(num_cores);

  // Setup
  if (core_id == 0) {
    printf("Initialize\n");

    // Create queue
    queue_create(&queue, 4);
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Producer
  if (core_id == 0) {
    int32_t data[QUEUE_DATA_SIZE];
    uint32_t counter = 0;
    for (uint32_t i = 0; i < 8; ++i) {
      for (uint32_t j = 0; j < QUEUE_DATA_SIZE; ++j) {
        data[j] = (int32_t)(i * QUEUE_DATA_SIZE + j);
      }
      blocking_queue_push(queue, data);
    }
    for (uint32_t i = 0; i < 8; ++i) {
      for (uint32_t j = 0; j < QUEUE_DATA_SIZE; ++j) {
        data[j] = (int32_t)(i * QUEUE_DATA_SIZE + j);
      }
      counting_queue_push(queue, data, &counter);
    }
    producer_cnt = counter;
  }

  // Consumer
  if (core_id == 1) {
    int32_t read_data[QUEUE_DATA_SIZE];
    uint32_t counter = 0;
    for (uint32_t i = 0; i < 8; ++i) {
      blocking_queue_pop(queue, read_data);
      for (uint32_t j = 0; j < QUEUE_DATA_SIZE; ++j) {
        printf("Rx: %d\n", read_data[j]);
      }
    }
    for (uint32_t i = 0; i < 8; ++i) {
      counting_queue_pop(queue, read_data, &counter);
      for (uint32_t j = 0; j < QUEUE_DATA_SIZE; ++j) {
        printf("Rx: %d\n", read_data[j]);
      }
    }
    consumer_cnt = counter;
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Destroy queue and print out counters
  if (core_id == 0) {
    queue_destroy(queue);
    printf("Stalls: %d/%d\n", producer_cnt, consumer_cnt);
  }

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
