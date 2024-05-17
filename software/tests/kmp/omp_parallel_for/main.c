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

TEST(omp_parallel_for_schedule_static) {
  int buf[64], *p;
  uint32_t i;
  int result = 0;
  memset(buf, '\0', sizeof(buf));

#pragma omp parallel for
  for (int i = 0; i < omp_get_num_threads(); i++) {
    buf[i] = i;
  }

  for (int i = 0; i < NUM_CORES; i++) {
    ASSERT_EQ(buf[i], i);
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3) private(p)
  for (p = &buf[10]; p < &buf[54]; p++) {
    *p = 5;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 5 * (i >= 10 && i < 54));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[3]; p <= &buf[63]; p += 2) {
    p[-2] = 6;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 6 * ((i & 1) && i <= 61));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[16]; p < &buf[51]; p = 4 + p) {
    p[2] = 7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[16]; p <= &buf[40]; p = p + 4U) {
    p[2] = -7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[53]; p > &buf[9]; --p) {
    *p = 5;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 5 * (i >= 10 && i < 54));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[63]; p >= &buf[3]; p -= 2) {
    p[-2] = 6;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 6 * ((i & 1) && i <= 61));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[48]; p > &buf[15]; p = -4 + p) {
    p[2] = 7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf[40]; p >= &buf[16]; p = p - 4U) {
    p[2] = -7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));
  }
}

TEST(parallel_for_schedule_static_thread) {
  uint32_t buf[NUM_CORES];

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for num_threads(4) schedule(static)
  for (int i = 0; i < 10; i++) {
    buf[i] = omp_get_thread_num();
  }

  int chunkSize = (10 + 4 - 1) / 4; // ceil(10/4)
  for (int i = 0; i < 10; i++) {
    ASSERT_EQ(buf[i], (i / chunkSize) % 4);
  }

  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for num_threads(4) schedule(static, 2)
  for (int i = 0; i < 10; i++) {
    buf[i] = omp_get_thread_num();
  }

  for (int i = 0; i < 10; i++) {
    ASSERT_EQ(buf[i], (i / 2) % 4);
  }

  int A = 9;
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for num_threads(4) schedule(static) private(A)
  for (int i = 0; i < 4; i++) {
    buf[i] = A;
    A = i;
  }

  for (int i = 0; i < 4; i++) {
    ASSERT_NEQ(buf[i], 9);
  }
  ASSERT_EQ(A, 9);

  A = 9;
  memset(buf, '\0', sizeof(buf));
#pragma omp parallel for num_threads(4) schedule(static) firstprivate(A)
  for (int i = 0; i < 4; i++) {
    buf[i] = A;
    A = i;
  }

  for (int i = 0; i < 4; i++) {
    ASSERT_EQ(buf[i], 9);
  }
  ASSERT_EQ(A, 9);

  A = 9;
#pragma omp parallel for num_threads(4) schedule(static) lastprivate(A)
  for (int i = 0; i < 4; i++) {
    A = i;
  }

  ASSERT_EQ(A, 3);
}

int main() {
  RUN_ALL_TESTS();
  PRINT_TEST_RESULTS();

  return 0;
}
