// Copyright 2024 ETH Zurich and University of Bologna.
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

TEST(test_teams_distribute) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int num_teams = 0;
    int team_num[12];

#pragma omp teams distribute num_teams(4)
    for (int i = 0; i < 12; i++) {
      team_num[i] = omp_get_team_num();

      if (omp_get_team_num() == 0) {
        num_teams = omp_get_num_teams();
      }
    }

    for (int i = 0; i < 12; i++) {
      ASSERT_EQ(team_num[i], i / 3);
    }

    ASSERT_EQ(num_teams, 4);
  }
}

TEST(test_teams_reduce) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int sum[4];

#pragma omp teams num_teams(4)
    {
      int local_sum = 0;

#pragma omp parallel for reduction(+ : local_sum)
      for (int i = 0; i < 32; i++) {
        local_sum += 1;
      }

      sum[omp_get_team_num()] = local_sum;
    }

    for (int i = 0; i < 4; i++) {
      ASSERT_EQ(sum[i], 32);
    }
  }
}

TEST(test_teams_barrier) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int results[2];
#pragma omp teams num_teams(2)
    {
      uint32_t team_num = omp_get_team_num();
      int result = 0;

#pragma omp parallel
      {
        uint32_t rank = omp_get_thread_num();
        if (rank == 1) {
          mempool_wait(1000); // give 1 sec to whole test
          result = 3;
        }
#pragma omp barrier

        if (rank == 2) {
          results[team_num] = result;
        }
      }
    }

    ASSERT_EQ(results[0], 3);
    ASSERT_EQ(results[1], 3);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
