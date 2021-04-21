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

// Must be a factor of SYSTOLIC_SIZE
#define QUEUE_DATA_SIZE 4

typedef struct {
  int32_t *buffer;
  uint32_t head;
  uint32_t tail;
  uint32_t counter;
  uint32_t size;
  uint32_t buffer_size;
} queue_t;

void queue_domain_create(alloc_t *alloc, queue_t **queue, const uint32_t size) {
  queue_t *new_queue = (queue_t *)domain_malloc(alloc, 6 * 4);
  uint32_t buffer_size = size * QUEUE_DATA_SIZE;
  int32_t *buffer = (int32_t *)domain_malloc(alloc, buffer_size * 4);
  new_queue->buffer = buffer;
  new_queue->head = 0;
  new_queue->tail = 0;
  new_queue->counter = 0;
  new_queue->size = size;
  new_queue->buffer_size = buffer_size;
  *queue = new_queue;
}

void queue_domain_destroy(alloc_t *alloc, queue_t *queue) {
  domain_free(alloc, queue->buffer);
  domain_free(alloc, queue);
}

void queue_create(queue_t **queue, const uint32_t size) {
  queue_domain_create(get_alloc_l1(), queue, size);
}

void queue_destroy(queue_t *queue) {
  queue_domain_destroy(get_alloc_l1(), queue);
}

int32_t queue_pop(queue_t *const queue, int32_t *data) {
  uint32_t current_head = queue->head;
  // Check if empty
  if (queue->counter == 0) {
    return 1;
  }
  // Copy data to data pointer
  int32_t *array = queue->buffer + current_head;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
  // Return success
  return 0;
}

int32_t queue_push(queue_t *const queue, int32_t *data) {
  uint32_t current_tail = queue->tail;
  uint32_t queue_size = queue->size;
  // Check if full
  if (queue->counter == queue_size) {
    return 1;
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
  // Return success
  return 0;
}

void blocking_queue_pop(queue_t *const queue, int32_t *data) {
  uint32_t current_head = queue->head;
  // Wait until not empty
  while (queue->counter == 0) {
    __asm__ __volatile__("");
  }
  // Copy data to data pointer
  int32_t *array = queue->buffer + current_head;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void blocking_queue_push(queue_t *const queue, int32_t *data) {
  uint32_t current_tail = queue->tail;
  uint32_t queue_size = queue->size;
  // Wait until not full
  while (queue->counter == queue_size) {
    __asm__ __volatile__("");
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void counting_queue_pop(queue_t *const queue, int32_t *data,
                        uint32_t *counter) {
  uint32_t current_head = queue->head;
  // Wait until not empty
  while (queue->counter == 0) {
    __asm__ __volatile__("");
    (*counter)++;
  }
  // Copy data to data pointer
  int32_t *array = queue->buffer + current_head;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void counting_queue_push(queue_t *const queue, int32_t *data,
                         uint32_t *counter) {
  uint32_t current_tail = queue->tail;
  uint32_t queue_size = queue->size;
  // Wait until not full
  while (queue->counter == queue_size) {
    __asm__ __volatile__("");
    (*counter)++;
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < QUEUE_DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + QUEUE_DATA_SIZE) % queue->buffer_size;
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}
