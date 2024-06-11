// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "baremetal/mempool_conv2d_i32p.h"
#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "testing.h"

#ifndef REPETITIONS
#define REPETITIONS 100 /* Number of times to run each test */
#endif

#define MAX_FACTOR 10
#define KNOWN_PRODUCT 3628800 /* 10! */
#define LOOPCOUNT 100 /* Number of iterations to split amongst threads */

int logics[LOOPCOUNT];

TEST(test_omp_parallel_for_sum) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int sum = 0;
    int known_sum = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;

#pragma omp parallel for schedule(static, 1) reduction(+ : sum)
    for (int i = 1; i <= LOOPCOUNT; i++) {
      sum += i;
    }

    ASSERT_EQ(sum, known_sum);
  }
}

TEST(test_omp_parallel_for_diff) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int diff = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;

#pragma omp parallel for schedule(static, 1) reduction(- : diff)
    for (int i = 1; i <= LOOPCOUNT; ++i) {
      diff -= i;
    }

    ASSERT_EQ(diff, 0);
  }
}

TEST(test_omp_parallel_for_product) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int product = 1;
    int known_product = KNOWN_PRODUCT;

#pragma omp parallel for schedule(static, 1) reduction(* : product)
    for (int i = 1; i <= MAX_FACTOR; i++) {
      product *= i;
    }

    ASSERT_EQ(product, known_product);
  }
}

TEST(test_omp_parallel_for_logic_and_part1) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int logic_and = 1;
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 1;
    }

#pragma omp parallel for schedule(static, 1) reduction(&& : logic_and)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logic_and = logic_and && logics[i];
    }

    ASSERT_EQ(logic_and, 1);
  }
}

TEST(test_omp_parallel_for_logic_and_part2) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int logic_and = 1;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 1;
    }
    logics[LOOPCOUNT / 2] = 0;

#pragma omp parallel for schedule(static, 1) reduction(&& : logic_and)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logic_and = logic_and && logics[i];
    }

    ASSERT_EQ(logic_and, 0);
  }
}

TEST(test_omp_parallel_for_logic_or_part1) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int logic_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }

#pragma omp parallel for schedule(static, 1) reduction(|| : logic_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logic_or = logic_or || logics[i];
    }

    ASSERT_EQ(logic_or, 0);
  }
}

TEST(test_omp_parallel_for_logic_or_part2) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int logic_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }
    logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static, 1) reduction(|| : logic_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logic_or = logic_or || logics[i];
    }

    ASSERT_EQ(logic_or, 1);
  }
}

TEST(test_omp_parallel_for_bit_and_part1) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int bit_and = 1;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logics[i] = 1;
    }

#pragma omp parallel for schedule(static, 1) reduction(& : bit_and)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      bit_and = bit_and & logics[i];
    }

    ASSERT_EQ(bit_and, 1);
  }
}

TEST(test_omp_parallel_for_bit_and_part2) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int bit_and = 1;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; ++i) {
      logics[i] = 1;
    }
    logics[LOOPCOUNT / 2] = 0;

#pragma omp parallel for schedule(static, 1) reduction(& : bit_and)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      bit_and = bit_and & logics[i];
    }

    ASSERT_EQ(bit_and, 0);
  }
}

TEST(test_omp_parallel_for_bit_or_part1) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int bit_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }

#pragma omp parallel for schedule(static, 1) reduction(| : bit_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      bit_or = bit_or | logics[i];
    }

    ASSERT_EQ(bit_or, 0);
  }
}

TEST(test_omp_parallel_for_bit_or_part2) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int bit_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }
    logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static, 1) reduction(| : bit_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      bit_or = bit_or | logics[i];
    }

    ASSERT_EQ(bit_or, 1);
  }
}

TEST(test_omp_parallel_for_exclusiv_bit_or_part1) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int exclusiv_bit_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }

#pragma omp parallel for schedule(static, 1) reduction(^ : exclusiv_bit_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
    }

    ASSERT_EQ(exclusiv_bit_or, 0);
  }
}

TEST(test_omp_parallel_for_exclusiv_bit_or_part2) {
  for (int rep = 0; rep < REPETITIONS; rep++) {
    int exclusiv_bit_or = 0;
    memset(logics, 0, LOOPCOUNT);
    for (int i = 0; i < LOOPCOUNT; i++) {
      logics[i] = 0;
    }
    logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static, 1) reduction(^ : exclusiv_bit_or)
    for (int i = 0; i < LOOPCOUNT; ++i) {
      exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
    }

    ASSERT_EQ(exclusiv_bit_or, 1);
  }
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
