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

#define REPETITIONS 10 /* Number of times to run each test */

TEST(test_omp_parallel_8) {
  for (int i = 0; i < REPETITIONS; i++) {
    printf("Master Thread: Parallel start\n");
    int nthreads = 0;

#pragma omp parallel num_threads(8)
    {
      nthreads = omp_get_num_threads();
      printf("%d\n", omp_get_num_threads());
    }
    printf("Master Thread: Parallel end\n\n\n");
    ASSERT_EQ(8, nthreads);
  }
}

TEST(test_omp_parallel) {
  for (int i = 0; i < REPETITIONS; i++) {
    printf("Master Thread: Parallel start\n");
    int nthreads = 0;

    printf("Master Thread: Parallel start\n");
#pragma omp parallel
    {
      nthreads = omp_get_num_threads();
      printf("%d\n", omp_get_num_threads());
    }
    printf("Master Thread: Parallel end\n\n\n");
    ASSERT_EQ(NUM_CORES, nthreads);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();

  return 0;
}
