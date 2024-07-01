// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "testing.h"

#ifndef REPETITIONS
#define REPETITIONS 100 /* Number of times to run each test */
#endif

TEST(test_omp_parallel_sections) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    uint32_t result = 0;
    uint32_t section_1 = 0;
    uint32_t section_2 = 0;

#pragma omp parallel sections
    {

#pragma omp section
      { section_1 = omp_get_thread_num(); }

#pragma omp section
      { section_2 = omp_get_thread_num(); }
    }

    ASSERT_NEQ(section_1, section_2);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
