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

#define REPETITIONS 1000 /* Number of times to run each test */
#define SLEEPTIME 1000

TEST(test_omp_barrier) {
  uint32_t result1;
  uint32_t result2;
  result1 = 0;
  result2 = 0;

  for (int i = 0; i < REPETITIONS; i++) {
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
#pragma omp barrier

      if (rank == 2) {
        printf("result2: %d\n", result2);
        result1 = result2;
        printf("result1: %d\n", result1);
      }
    }
    ASSERT_EQ(result1, 3);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
