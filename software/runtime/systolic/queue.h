// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

/* This library implements the single-producer single-consumer queue
 */

// Concurrent single-producer single-consumer queue based on head and tail
// Uses a single slot buffer for the full state to differentiate it from empty

#include "alloc.h"
#include "runtime.h"

typedef struct {
  int32_t *array;
  uint32_t volatile head;
  uint32_t volatile tail;
  uint32_t size;
} queue_t;

void queue_domain_create(alloc_t *alloc, queue_t **queue, const uint32_t size) {
  queue_t *new_queue = (queue_t *)domain_malloc(alloc, 4 * 4);
  int32_t *array = (int32_t *)domain_malloc(alloc, size * 4);
  new_queue->array = array;
  new_queue->head = 0;
  new_queue->tail = 0;
  new_queue->size = size;
  *queue = new_queue;
}

void queue_domain_destroy(alloc_t *alloc, queue_t *queue) {
  domain_free(alloc, queue->array);
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
  };
}

void blocking_queue_push(queue_t *const queue, int32_t *data) {
  while (queue_push(queue, data)) {
  };
}

void counting_queue_pop(queue_t *const queue, int32_t *data,
                        uint32_t *counter) {
  while (queue_pop(queue, data)) {
    (*counter)++;
  };
}

void counting_queue_push(queue_t *const queue, int32_t *data,
                         uint32_t *counter) {
  while (queue_push(queue, data)) {
    (*counter)++;
  };
}
