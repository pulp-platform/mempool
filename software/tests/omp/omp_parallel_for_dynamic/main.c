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

int buf[64];

TEST(gcc_omp_parallel_for_schedule_dynamic) {
  int i, j;

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 10; j < 54; j++)
    buf[j] = 5;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 5 * (i >= 10 && i < 54));

  DEBUG_PRINT("First\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 3; j <= 63; j += 2)
    buf[j - 2] = 6;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 6 * ((i & 1) && i <= 61));

  DEBUG_PRINT("Second\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 16; j < 51; j += 4)
    buf[j + 2] = 7;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));

  DEBUG_PRINT("Third\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 16; j <= 40; j += 4)
    buf[j + 2] = -7;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));

  DEBUG_PRINT("Fourth\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 53; j > 9; --j) {
    DEBUG_PRINT("%d\n", j);
    buf[j] = 5;
  }

  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 5 * (i >= 10 && i < 54));

  DEBUG_PRINT("Fifth\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 63; j >= 3; j -= 2)
    buf[j - 2] = 6;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 6 * ((i & 1) && i <= 61));

  DEBUG_PRINT("Sixth\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 48; j > 15; j -= 4)
    buf[j + 2] = 7;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));

  DEBUG_PRINT("Seventh\n");

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(dynamic, 3)
  for (j = 40; j >= 16; j -= 4)
    buf[j + 2] = -7;
  for (i = 0; i < 64; i++)
    ASSERT_EQ(buf[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));

  DEBUG_PRINT("Eighth\n");
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();

  return 0;
}
