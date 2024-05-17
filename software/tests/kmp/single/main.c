// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "testing.h"

#define REPETITIONS 10 /* Number of times to run each test */

TEST(test_omp_parallel_single) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    uint32_t result = 0;

#pragma omp parallel shared(result)
    {

#pragma omp single
      { result += 100; }
    }

    ASSERT_EQ(result, 100);
  }
}

TEST(test_omp_for_single) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
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

    ASSERT_EQ(sum, 1);
  }
}

TEST(test_omp_single_copyprivate) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    uint32_t result = 0;
    uint32_t outerResult = 0;

#pragma omp parallel private(result)
    {

#pragma omp single copyprivate(result)
      { result = 100; }

#pragma omp single
      { outerResult = result; }
    }

    ASSERT_EQ(outerResult, 100);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
