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
#include "testing.h"

#ifndef REPETITIONS
#define REPETITIONS 100 /* Number of times to run each test */
#endif

TEST(test_omp_parallel_for) {
  for (int i = 0; i < REPETITIONS; i++) {
    int sum = 0;

#pragma omp parallel shared(sum)
    {
#pragma omp for reduction(+ : sum)
      for (int i = 0; i <= 100; i++) {
        sum += i;
      }
    }

    ASSERT_EQ(sum, 5050);
  }
}

TEST(test_omp_parallel_for_dynamic) {
  for (int i = 0; i < REPETITIONS; i++) {
    int sum = 0;

#pragma omp parallel shared(sum)
    {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
      for (int i = 0; i <= 100; i++) {
        sum += i;
      }
    }

    ASSERT_EQ(sum, 5050);
  }
}

TEST(test_omp_parallel_for_dynamic_static) {
  for (int i = 0; i < REPETITIONS; i++) {
    int sum = 0;
    int sum1, sum2 = 0;

#pragma omp parallel shared(sum)
    {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
      for (int i = 0; i <= 100; i++) {
        sum += i;
      }

#pragma omp single
      sum = 0;

#pragma omp for schedule(static) reduction(+ : sum)
      for (int i = -100; i <= 0; i++) {
        sum += i;
      }
    }

    printf("sum: %d\n", sum);
    ASSERT_EQ(sum, -5050);
  }
}

TEST(test_omp_many) {
  for (int i = 0; i < REPETITIONS; i++) {
    int sum = 0;
    int master_sum, single_sum = 0;

#pragma omp parallel shared(sum)
    {
#pragma omp for schedule(dynamic, 16) reduction(+ : sum)
      for (int i = 0; i <= 100; i++) {
        sum += i;
      }

#pragma omp barrier

#pragma omp master
      { master_sum = sum; }

#pragma omp barrier

#pragma omp for schedule(static) reduction(+ : sum)
      for (int i = -10; i <= 0; i++) {
        sum += i;
      }

#pragma omp barrier

#pragma omp single
      { single_sum = sum; }
    }

    ASSERT_EQ(master_sum, 5050);
    ASSERT_EQ(single_sum, 4995);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
