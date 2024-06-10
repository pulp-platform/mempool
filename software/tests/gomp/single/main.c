// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define REPETITIONS 10 /* Number of times to run each test */

void work1() {
  int sum = 0;
  for (int i = 0; i < 100; i++) {
    sum++;
  }
}

uint32_t test_omp_parallel_single() {
  uint32_t result;
  result = 0;
  uint32_t core_id;

#pragma omp parallel shared(result)
  {
    core_id = mempool_get_core_id();

    work1();
    if (core_id == 0) {
      work1();
    }

#pragma omp single
    { result = 100; }

    work1();
    if (core_id == 0) {
      work1();
    }

#pragma omp single
    {
      if (result == 100)
        result = core_id;
    }
  }
  return result;
}

uint32_t test_omp_for_single() {
  uint32_t sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp single
    {
      for (uint32_t i = 0; i <= 100; i++) {
        sum += i;
      }
    }
#pragma omp single
    {
      if (sum == 100 * 101 / 2)
        sum = 1;
    }
  }
  return sum;
}

uint32_t test_omp_single_copyprivate() {
  uint32_t result;
  result = 0;

#pragma omp parallel firstprivate(result)
  {
    uint32_t core_id = mempool_get_core_id();

    work1();
    if (core_id == 0) {
      work1();
    }

#pragma omp single copyprivate(result)
    { result = 100; }

    work1();
    if (core_id == 5) {
      result *= 2;
      printf("Core 5 result: %d\n", result);
    }
  }
  return result;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t i;

  if (core_id == 0) {
    printf("Master Thread start\n");
    for (i = 0; i < REPETITIONS; i++) {
      printf("Test: %d\n", i);
      printf("Single core_id: %d\n", test_omp_parallel_single());
      printf("For loop-sum is t/f: %d\n", test_omp_for_single());
      printf("Copyprivate: %d\n", test_omp_single_copyprivate());
      printf("Test finished: %d\n", i);
    }
    printf("Master Thread end\n\n\n");
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
