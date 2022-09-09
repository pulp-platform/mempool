// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include "halide_runtime.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wunused-parameter"

typedef struct {
  halide_task_t task;
  uint8_t *closure;
  void *user_context;
  uint32_t size;
  uint32_t barrier;
} halide_parallel_task_t;

halide_parallel_task_t halide_parallel_task __attribute__((section(".l1")));

void *halide_malloc(void *user_context, size_t x) { return simple_malloc(x); }

void halide_free(void *user_context, void *ptr) { simple_free(ptr); }

char *getenv(const char *name) { return NULL; };

void halide_error(void *user_context, const char *msg) {
  halide_print(user_context, msg);
}

size_t write(int fd, const void *buf, size_t count) {
  const char *msg = buf;
  printf("Write is not implemented! fd: %d\n", fd);
  for (unsigned i = 0; i < count; ++i) {
    printf("%c", msg[count]);
  }
  printf("\n");
  return 1;
}

FILE *fopen(const char *pathname, const char *mode) {
  printf("fopen not implemented!\n");
  return (FILE *)NULL;
}

size_t fwrite(const void *ptr, size_t size, size_t count, FILE *stream) {
  printf("fwrite not implemented!\n");
  return 0;
}

int fclose(FILE *stream) {
  printf("fclose not implemented!\n");
  return -1;
}

int fileno(FILE *stream) {
  printf("fileno not implemented!\n");
  return -1;
}

int atoi(const char *str) {
  printf("atoi not implemented!\n");
  return 0;
}

void halide_print(void *user_context, const char *msg) { printf("%s\n", msg); }

//////////////
// Parallel //
//////////////

// Execute one chunk of the parallelized task
// static inline halide_run_parallel_task()

// Halide calls this function
int halide_do_par_for(void *user_context, halide_task_t task, int min, int size,
                      uint8_t *closure) {
  // Debug
  printf("Halide_do_par_for %x %x %d %d %x!\n", user_context, task, min, size,
         closure);
  // Initialize the parallel task struct for the slave cores
  halide_parallel_task.task = task;
  halide_parallel_task.closure = closure;
  halide_parallel_task.user_context = user_context;
  halide_parallel_task.size = size;
  halide_parallel_task.barrier = NUM_CORES;
  // Wake up the threadpool
  __sync_synchronize(); // Full memory barrier
  wake_up_all();
  mempool_wfi();
  // Participate in the threadpool
  for (uint32_t i = mempool_get_core_id(); i < size;
       i += mempool_get_core_count()) {
    task(user_context, (int32_t)i, closure);
  }
  if (__atomic_fetch_sub(&halide_parallel_task.barrier, 1, __ATOMIC_SEQ_CST) ==
      1) {
    wake_up_all();
  }
  mempool_wfi();
  return 0;
}

void halide_slave_core() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  while (1) {
    mempool_wfi();
    for (uint32_t i = core_id; i < halide_parallel_task.size; i += num_cores) {
      halide_parallel_task.task(halide_parallel_task.user_context, (int32_t)i,
                                halide_parallel_task.closure);
    }
    if (__atomic_fetch_sub(&halide_parallel_task.barrier, 1,
                           __ATOMIC_SEQ_CST) == 1) {
      wake_up_all();
    }
    mempool_wfi();
  }
}

#pragma GCC diagnostic pop
