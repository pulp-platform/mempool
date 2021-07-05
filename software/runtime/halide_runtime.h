// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#ifndef __HALIDE_RUNTIME_H__
#define __HALIDE_RUNTIME_H__

#include "HalideRuntime.h"
#include <stdio.h>

void *halide_malloc(void *user_context, size_t x);
void halide_free(void *user_context, void *ptr);
char *getenv(const char *name);
size_t write(int fd, const void *buf, size_t count);
FILE *fopen(const char *pathname, const char *mode);
size_t fwrite(const void *ptr, size_t size, size_t count, FILE *stream);
int fclose(FILE *stream);
int fileno(FILE *stream);
int atoi(const char *str);
void halide_print(void *user_context, const char *msg);
int halide_do_par_for(void *user_context, halide_task_t task, int min, int size,
                      uint8_t *closure);

#endif // __HALIDE_RUNTIME_H__
