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

#define REPETITIONS 1 /* Number of times to run each test */

void work1() {
  int sum = 0;
  for (int i = 0; i < 100; i++) {
    sum++;
  }
}

int test_omp_parallel_for() {
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
  }
  return sum;
}

int test_omp_parallel_for_dynamic() {
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }
  }
  return sum;
}

int test_omp_parallel_for_dynamic_static() {
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }

    sum = 0;
#pragma omp for schedule(static) reduction(+ : sum)
    for (int i = -100; i <= 0; i++) {
      sum += i;
    }
  }
  return sum;
}

int test_omp_many() {
  int sum = 0;

#pragma omp parallel shared(sum)
  {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
    for (int i = 0; i <= 100; i++) {
      sum += i;
    }

#pragma omp barrier

#pragma omp master
    {
      printf("first sum: %d\n", sum);
      sum = 0;
    }

#pragma omp barrier

#pragma omp for schedule(static) reduction(+ : sum)
    for (int i = -10; i <= 0; i++) {
      sum += i;
    }

#pragma omp barrier

#pragma omp single
    { printf("second sum: %d\n", sum); }
  }
  return sum;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t i;

  printf("Master Thread start\n");
  for (i = 0; i < REPETITIONS; i++) {
    printf("Test: %d\n", i);
    printf("For loop-sum is: %d\n", test_omp_parallel_for());
    printf("For loop dynamic-sum is: %d\n", test_omp_parallel_for_dynamic());
    printf("For loop dynamic-static-sum is: %d\n",
           test_omp_parallel_for_dynamic_static());
    printf("Test many omp-sum is: %d\n", test_omp_many());
    printf("Test finished: %d\n", i);
  }
  printf("Master Thread end\n\n\n");

  return 0;
}
