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

TEST(test_omp_master) {
  for (int i = 0; i < REPETITIONS; i++) {

    uint32_t nthreads;
    int32_t executing_thread;
    // counts up the number of wrong thread no. for the master thread. (Must be
    // 0)
    uint32_t tid = 0;
    nthreads = 0;
    executing_thread = -1;

#pragma omp parallel
    {
#pragma omp master
      {
        printf("Master Thread executes\n\n\n");
        tid = omp_get_thread_num();
        nthreads++;
        executing_thread = (int32_t)omp_get_thread_num();
      } /* end of master*/
    }   /* end of parallel*/

    ASSERT_EQ(1, nthreads);
    ASSERT_EQ(0, executing_thread);
    ASSERT_EQ(0, tid);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();

  return 0;
}
