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

TEST(test_omp_critical) {
  int num_cores = (int)mempool_get_core_count();

  for (int r = 0; r < REPETITIONS; r++) {
    int sum1 = 0;
    int sum2 = 0;

#pragma omp parallel
    {
#pragma omp critical
      {
        sum1 += 1;
        sum2 += 2;
      }

#pragma omp critical
      {
        sum1 += 1;
        sum2 += 2;
      }
    }

    ASSERT_EQ(sum1, 2 * num_cores);
    ASSERT_EQ(sum2, 2 * sum1);
    ASSERT_EQ(sum2, 4 * num_cores);
  }
}

int main() {
  RUN_ALL_TESTS();
  return 0;
}
