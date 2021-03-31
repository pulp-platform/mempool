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

/* This library implements the single-producer single-consumer queue
 */

// Concurrent single-producer single-consumer queue based on head and tail
// Uses a single slot buffer for the full state to differentiate it from empty

#include "alloc.h"
#include "runtime.h"

typedef struct {
  int32_t *array;
  uint32_t head;
  uint32_t tail;
  uint32_t size;
} queue_t;

void queue_create(queue_t **queue, const uint32_t size) {
  queue_t *new_queue = (queue_t *)simple_malloc(4 * 4);
  int32_t *array = (int32_t *)simple_malloc(size * 4);
  new_queue->array = array;
  new_queue->head = 0;
  new_queue->tail = 0;
  new_queue->size = size;
  *queue = new_queue;
}

void queue_destroy(queue_t *queue) {
  simple_free(queue->array);
  simple_free(queue);
}

int32_t queue_pop(queue_t *const queue, int32_t *data) {
  uint32_t current_head = queue->head;
  // Check if empty
  if (current_head == queue->tail) {
    return 1;
  }
  // Read data
  *data = queue->array[current_head];
  // Update head
  queue->head = (current_head + 1) % queue->size;
  return 0;
}

int32_t queue_push(queue_t *const queue, int32_t *data) {
  uint32_t current_tail = queue->tail;
  uint32_t next_tail = (current_tail + 1) % queue->size;
  // Check if full (with one slot constantly open)
  if (next_tail == queue->head) {
    return 1;
  }
  // Write data
  queue->array[current_tail] = *data;
  __asm__ __volatile__("" : : : "memory");
  // Safely update tail
  queue->tail = next_tail;
  return 0;
}

void blocking_queue_pop(queue_t *const queue, int32_t *data) {
  while (queue_pop(queue, data)) {
    mempool_wait(1);
  };
}

void blocking_queue_push(queue_t *const queue, int32_t *data) {
  while (queue_push(queue, data)) {
    mempool_wait(1);
  };
}

uint32_t counting_queue_pop(queue_t *const queue, int32_t *data) {
  uint32_t counter = 0;
  while (queue_pop(queue, data)) {
    counter++;
  };
  return counter;
}

uint32_t counting_queue_push(queue_t *const queue, int32_t *data) {
  uint32_t counter = 0;
  while (queue_push(queue, data)) {
    counter++;
  };
  return counter;
}