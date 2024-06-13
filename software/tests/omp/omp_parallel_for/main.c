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

int buf_1[64];
uint32_t buf_2[NUM_CORES];

TEST(omp_parallel_for_schedule_static) {
  uint32_t i;
  int *p;
  int result = 0;
  memset(buf_1, '\0', sizeof(buf_1));

#pragma omp parallel for
  for (int i = 0; i < omp_get_num_threads(); i++) {
    buf_1[i] = i;
  }

  for (int i = 0; i < NUM_CORES; i++) {
    ASSERT_EQ(buf_1[i], i);
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3) private(p)
  for (p = &buf_1[10]; p < &buf_1[54]; p++) {
    *p = 5;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 5 * (i >= 10 && i < 54));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[3]; p <= &buf_1[63]; p += 2) {
    p[-2] = 6;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 6 * ((i & 1) && i <= 61));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[16]; p < &buf_1[51]; p = 4 + p) {
    p[2] = 7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[16]; p <= &buf_1[40]; p = p + 4U) {
    p[2] = -7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[53]; p > &buf_1[9]; --p) {
    *p = 5;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 5 * (i >= 10 && i < 54));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[63]; p >= &buf_1[3]; p -= 2) {
    p[-2] = 6;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 6 * ((i & 1) && i <= 61));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[48]; p > &buf_1[15]; p = -4 + p) {
    p[2] = 7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], 7 * ((i & 3) == 2 && i >= 18 && i < 53));
  }

  memset(buf_1, '\0', sizeof(buf_1));
#pragma omp parallel for schedule(static, 3)
  for (p = &buf_1[40]; p >= &buf_1[16]; p = p - 4U) {
    p[2] = -7;
  }

  for (i = 0; i < 64; i++) {
    ASSERT_EQ(buf_1[i], -7 * ((i & 3) == 2 && i >= 18 && i <= 42));
  }
}

TEST(parallel_for_schedule_static_thread) {

  memset(buf_2, '\0', sizeof(buf_2));
#pragma omp parallel for num_threads(4) schedule(static)
  for (int i = 0; i < 10; i++) {
    buf_2[i] = omp_get_thread_num();
  }

  int chunkSize = (10 + 4 - 1) / 4; // ceil(10/4)
  for (int i = 0; i < 10; i++) {
    ASSERT_EQ(buf_2[i], (i / chunkSize) % 4);
  }

  memset(buf_2, '\0', sizeof(buf_2));
#pragma omp parallel for num_threads(4) schedule(static, 2)
  for (int i = 0; i < 10; i++) {
    buf_2[i] = omp_get_thread_num();
  }

  for (int i = 0; i < 10; i++) {
    ASSERT_EQ(buf_2[i], (i / 2) % 4);
  }

  int A = 9;
  memset(buf_2, '\0', sizeof(buf_2));
#pragma omp parallel for num_threads(4) schedule(static) private(A)
  for (int i = 0; i < 4; i++) {
    buf_2[i] = A;
    A = i;
  }

  for (int i = 0; i < 4; i++) {
    ASSERT_NEQ(buf_2[i], 9);
  }
  ASSERT_EQ(A, 9);

  A = 9;
  memset(buf_2, '\0', sizeof(buf_2));
#pragma omp parallel for num_threads(4) schedule(static) firstprivate(A)
  for (int i = 0; i < 4; i++) {
    buf_2[i] = A;
    A = i;
  }

  for (int i = 0; i < 4; i++) {
    ASSERT_EQ(buf_2[i], 9);
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
