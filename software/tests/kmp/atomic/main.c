// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "../../runtime/testing.h"
#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define REPETITIONS 100 /* Number of times to run each test */
#define MAX_FACTOR 10
#define KNOWN_PRODUCT 3628800 /* 10! */
#define LOOPCOUNT 100         /* Number of iterations to slit amongst threads */

TEST(sum_of_integers) {
  for (int count = 0; count < REPETITIONS; count++) {
    int sum = 0;

#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 1; i <= LOOPCOUNT; i++) {
#pragma omp atomic
        sum += i;
      }
    }

    int known_sum = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;
    ASSERT_EQ(known_sum, sum);
  }
}

TEST(difference_of_integers) {
  for (int count = 0; count < REPETITIONS; count++) {
    int diff = 0;

#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 0; i < LOOPCOUNT; i++) {
#pragma omp atomic
        diff -= i;
      }
    }

    int known_diff = ((LOOPCOUNT - 1) * LOOPCOUNT) / 2 * -1;
    printf("known_diff: %d, diff: %d\n", known_diff, diff);
    ASSERT_EQ(known_diff, diff);
  }
}

TEST(product_of_integers) {
  for (int count = 0; count < REPETITIONS; count++) {
    int product = 1;

#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 1; i <= MAX_FACTOR; i++) {
#pragma omp atomic
        product *= i;
      }
    }

    ASSERT_EQ(KNOWN_PRODUCT, product);
  }
}

TEST(division_of_integers) {
  for (int count = 0; count < REPETITIONS; count++) {
    int product = KNOWN_PRODUCT;

#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 1; i <= MAX_FACTOR; ++i) {
#pragma omp atomic
        product /= i;
      }
    }

    ASSERT_EQ(1, product);
  }
}

TEST(atomic_increment) {
  int x = 0;

  for (int count = 0; count < REPETITIONS; count++) {

    x = 0;
#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
        x++;
      }
    }

    ASSERT_EQ(LOOPCOUNT, x);
  }
}

TEST(atomic_decrement) {
  int x = 0;

  for (int count = 0; count < REPETITIONS; count++) {

    x = LOOPCOUNT;
#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
        x--;
      }
    }

    ASSERT_EQ(0, x);
  }
}

TEST(atomic_bit_and_1) {
  int logics[LOOPCOUNT];
  int bit_and = 1;

  for (int count = 0; count < REPETITIONS; count++) {

    for (int j = 0; j < LOOPCOUNT; ++j) {
      logics[j] = 1;
    }
    bit_and = 1;
#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
        bit_and &= logics[i];
      }
    }

    ASSERT_EQ(1, bit_and);
  }
}

TEST(atomic_bit_and_2) {
  int logics[LOOPCOUNT];
  int bit_and = 1;

  for (int count = 0; count < REPETITIONS; count++) {

    bit_and = 1;
    logics[LOOPCOUNT / 2] = 0;
#pragma omp parallel
    {
      int i;
#pragma omp for
      for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
        bit_and &= logics[i];
      }
    }

    ASSERT_EQ(0, bit_and);
  }
}

TEST(atomic_bit_or_1) {
  int logics[LOOPCOUNT];
  int bit_or = 1;

  for (int j = 0; j < LOOPCOUNT; j++) {
    logics[j] = 0;
  }

  bit_or = 0;
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      bit_or |= logics[i];
    }
  }

  ASSERT_EQ(0, bit_or);
}

TEST(atomic_bit_or_2) {
  int logics[LOOPCOUNT];
  int bit_or = 1;

  for (int j = 0; j < LOOPCOUNT; j++) {
    logics[j] = 0;
  }

  bit_or = 0;
  logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel
  {

    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      bit_or |= logics[i];
    }
  }
  ASSERT_EQ(1, bit_or);
}

TEST(atomix_bit_xor_1) {
  int logics[LOOPCOUNT];
  int exclusiv_bit_or = 0;
  for (int j = 0; j < LOOPCOUNT; j++) {
    logics[j] = 0;
  }

#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      exclusiv_bit_or ^= logics[i];
    }
  }

  ASSERT_EQ(0, exclusiv_bit_or);
}

TEST(atomic_bit_xor_2) {
  int logics[LOOPCOUNT];
  int exclusiv_bit_or = 0;

  for (int j = 0; j < LOOPCOUNT; j++) {
    logics[j] = 0;
  }

  exclusiv_bit_or = 0;
  logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      exclusiv_bit_or ^= logics[i];
    }
  }

  ASSERT_EQ(1, exclusiv_bit_or);
}
//
TEST(atomic_left_shift) {
  int x = 1;

#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < 10; ++i) {
#pragma omp atomic
      x <<= 1;
    }
  }

  ASSERT_EQ(1024, x);
}

TEST(atomic_right_shift) {
  int x = 1024;

#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < 10; ++i) {
#pragma omp atomic
      x >>= 1;
    }
  }

  ASSERT_EQ(1, x);
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();
}
