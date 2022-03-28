// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "alloc.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "systolic/queue_multi.h"

// IMPORTANT: DATA_SIZE of queue_multi.h must be set to 4

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
    queue_create(&queue);
  }

  // Wait for all cores
  mempool_barrier(num_cores);

  // Producer
  if (core_id == 0) {
    int32_t data[4];
    uint32_t counter = 0;
    for (uint32_t i = 0; i < 8; ++i) {
      for (uint32_t j = 0; j < 4; ++j) {
        data[j] = (int32_t)(i * 4 + j);
      }
      blocking_queue_push(queue, data);
    }
    for (uint32_t i = 0; i < 8; ++i) {
      for (uint32_t j = 0; j < 4; ++j) {
        data[j] = (int32_t)(i * 4 + j);
      }
      counting_queue_push(queue, data, &counter);
    }
    producer_cnt = counter;
  }

  // Consumer
  if (core_id == 1) {
    int32_t read_data[4];
    uint32_t counter = 0;
    for (uint32_t i = 0; i < 8; ++i) {
      blocking_queue_pop(queue, read_data);
      for (uint32_t j = 0; j < 4; ++j) {
        printf("Rx: %d\n", read_data[j]);
      }
    }
    for (uint32_t i = 0; i < 8; ++i) {
      counting_queue_pop(queue, read_data, &counter);
      for (uint32_t j = 0; j < 4; ++j) {
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
