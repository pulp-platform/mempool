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

void *halide_malloc(void *user_context, size_t x) { return (void *)0x0000b000; }

void halide_free(void *user_context, void *ptr) {}

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

// Halide calls this function
int halide_do_par_for(void *user_context, halide_task_t task, int min, int size,
                      uint8_t *closure) {
  for (uint32_t core_id = mempool_get_core_id(); core_id < (uint32_t)size;
       core_id += mempool_get_core_count()) {
    task(user_context, (int32_t)core_id, closure);
  }

  return 0;
}

#pragma GCC diagnostic pop
