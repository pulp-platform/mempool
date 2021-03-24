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

// Author: Gua Hao Khov, ETH Zurich

/* This library implements the single-producer single-consumer queue
 */

// CONCURRENT QUEUE BASED ON AMO ADD/SUB (SINGLE PRODUCER, SINGLE CONSUMER)
// DO WE HAVE ATOMIC MODULO ADDITION OR ATOMIC SET?

struct queue_t {
  int32_t *array;
  uint32_t head;
  uint32_t tail;
  uint32_t size;
};

/*
void queue_create(struct queue_t *queue, uint32_t size) {
  struct queue_t new_queue;
  queue = &new_queue;
  int32_t data[size];
  queue->array = data;
  queue->head = 0;
  queue->tail = 0;
  queue->size = size;
}
*/

int32_t queue_pop(struct queue_t *const queue, int32_t *data) {
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

int32_t queue_push(struct queue_t *const queue, int32_t *data) {
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
