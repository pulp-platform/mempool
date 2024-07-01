// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

int32_t dot_product_omp_static(int32_t const *__restrict__ A,
                               int32_t const *__restrict__ B,
                               uint32_t num_elements) {
  uint32_t i;
  int32_t dotp = 0;
#pragma omp parallel for reduction(+ : dotp)
  for (i = 0; i < num_elements; i++) {
    dotp += A[i] * B[i];
  }
  return dotp;
}

int32_t dot_product_omp_dynamic(int32_t const *__restrict__ A,
                                int32_t const *__restrict__ B,
                                uint32_t num_elements) {
  uint32_t i;
  int32_t dotp = 0;
  // printf("num_elements %d\n", num_elements);
#pragma omp parallel for schedule(dynamic) reduction(+ : dotp)
  for (i = 0; i < num_elements; i++) {
    dotp += A[i] * B[i];
  }
  return dotp;
}

int main() {
  uint32_t num_cores = mempool_get_core_count();
  mempool_timer_t cycles;

  mempool_wait(4 * num_cores);

  for (unsigned int i = 1; i <= 8192; i *= 2) {
    int32_t *a = simple_malloc(i * sizeof(int32_t));
    cycles = mempool_get_timer();
    dot_product_omp_static(a, a, i);
    cycles = mempool_get_timer() - cycles;
    simple_free(a);
    printf("Static duration with %d elements: %d\n", i, cycles);
  }

  for (unsigned int i = 1; i <= 8192; i *= 2) {
    int32_t *a = simple_malloc(i * sizeof(int32_t));
    cycles = mempool_get_timer();
    dot_product_omp_dynamic(a, a, i);
    cycles = mempool_get_timer() - cycles;
    simple_free(a);
    printf("Dynamic duration with %d elements: %d\n", i, cycles);
  }

  return 0;
}
