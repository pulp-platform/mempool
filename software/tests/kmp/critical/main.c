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

#define REPETITIONS 10 /* Number of times to run each test */

int test_omp_critical() {
  int sum;
  int known_sum, mysum;
  int num_cores = (int)mempool_get_core_count();

  sum = 0;
#pragma omp parallel
  {
    mysum = 0;
    int i;

#pragma omp single
    {
      for (i = 0; i < 100; i++) {
        mysum = mysum + i;
      }
      printf("Single mysum: %d, thread_id: %d\n", mysum, omp_get_thread_num());
    }

#pragma omp critical
    {
      sum = mysum + sum;
      printf("Critical mysum: %d, sum: %d, thread_id: %d\n", mysum, sum,
             omp_get_thread_num());
    }
  }

  known_sum = 99 * 100 / 2 * num_cores;
  printf("sum: %d, known_sum: %d\n", sum, known_sum);
  return (known_sum == sum);
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i;
  uint32_t num_failed = 0;

  mempool_wait(2 * num_cores);

  printf("Master Thread start\n");
  for (i = 0; i < REPETITIONS; i++) {
    printf("test: %d\n", i);
    if (!test_omp_critical()) {
      num_failed++;
    }
    printf("num_failed: %d\n", num_failed);
  }
  printf("Master Thread end\n\n\n");
  printf("num_failed: %d\n", num_failed);

  return 0;
}
