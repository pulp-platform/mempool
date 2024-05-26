// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "runtime.h"
#include "omp.h"
#include "printf.h"
#include "synchronization.h"

#define REPETITIONS 1000 /* Number of times to run each test */
#define SLEEPTIME 1000

uint32_t test_omp_barrier(uint32_t num_cores) {
  uint32_t result1;
  uint32_t result2;
  result1 = 0;
  result2 = 0;

#pragma omp parallel
  {
    uint32_t rank;
    rank = omp_get_thread_num();
    if (rank == 1) {
      printf("waiting...\n");
      mempool_wait(((double)SLEEPTIME) /
                   REPETITIONS); // give 1 sec to whole test
      printf("waited.\n");
      result2 = 3;
    }
    mempool_barrier(num_cores);

    if (rank == 2) {
      printf("result2: %d\n", result2);
      result1 = result2;
      printf("result1: %d\n", result1);
    }
  }
  return (result1 == 3);
}

int main() {
  uint32_t num_cores = mempool_get_core_count();
  uint32_t i;
  uint32_t num_failed = 0;

  printf("Master Thread start\n");
  for (i = 0; i < REPETITIONS; i++) {
    printf("test: %d\n", i);
    if (!test_omp_barrier(num_cores)) {
      num_failed++;
    }
    printf("test finished: %d\n", i);
  }
  printf("Master Thread end\n\n\n");
  printf("num_failed: %d\n", num_failed);

  return 0;
}
