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

#define DATA_SIZE 4

typedef struct {
  int32_t *buffer;
  uint32_t head;
  uint32_t tail;
  uint32_t volatile counter;
} queue_t;

void queue_domain_create(alloc_t *alloc, queue_t **queue) {
  queue_t *new_queue = (queue_t *)domain_malloc(alloc, 4 * 4);
  int32_t *buffer =
      (int32_t *)domain_malloc(alloc, XQUEUE_SIZE * DATA_SIZE * 4);
  new_queue->buffer = buffer;
  new_queue->head = 0;
  new_queue->tail = 0;
  new_queue->counter = 0;
  *queue = new_queue;
}

void queue_domain_destroy(alloc_t *alloc, queue_t *queue) {
  domain_free(alloc, queue->buffer);
  domain_free(alloc, queue);
}

void queue_create(queue_t **queue) {
  queue_domain_create(get_alloc_l1(), queue);
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
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
  // Return success
  return 0;
}

int32_t queue_push(queue_t *const queue, int32_t *data) {
  uint32_t current_tail = queue->tail;
  // Check if full
  if (queue->counter == XQUEUE_SIZE) {
    return 1;
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
  // Return success
  return 0;
}

void blocking_queue_pop(queue_t *const queue, int32_t *data) {
  uint32_t current_head = queue->head;
  // Wait until not empty
  while (queue->counter == 0) {
  }
  // Copy data to data pointer
  int32_t *array = queue->buffer + current_head;
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void blocking_queue_push(queue_t *const queue, int32_t *data) {
  uint32_t current_tail = queue->tail;
  // Wait until not full
  while (queue->counter == XQUEUE_SIZE) {
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void counting_queue_pop(queue_t *const queue, int32_t *data,
                        uint32_t *counter) {
  uint32_t current_head = queue->head;
  // Wait until not empty
  while (queue->counter == 0) {
    (*counter)++;
  }
  // Copy data to data pointer
  int32_t *array = queue->buffer + current_head;
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    data[i] = array[i];
  }
  // Update head
  queue->head = (current_head + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_sub(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}

void counting_queue_push(queue_t *const queue, int32_t *data,
                         uint32_t *counter) {
  uint32_t current_tail = queue->tail;
  // Wait until not full
  while (queue->counter == XQUEUE_SIZE) {
    (*counter)++;
  }
  // Copy data from data pointer
  int32_t *array = queue->buffer + current_tail;
  for (uint32_t i = 0; i < DATA_SIZE; ++i) {
    array[i] = data[i];
  }
  // Update tail
  queue->tail = (current_tail + DATA_SIZE) % (XQUEUE_SIZE * DATA_SIZE);
  // Update counter
  __atomic_fetch_add(&(queue->counter), 1, __ATOMIC_SEQ_CST);
}
