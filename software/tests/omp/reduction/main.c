// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "baremetal/mempool_conv2d_i32p.h"
#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define REPETITIONS 10 /* Number of times to run each test */

#define MAX_FACTOR 10
#define KNOWN_PRODUCT 3628800 /* 10! */
#define LOOPCOUNT 100         /* Number of iterations to slit amongst threads */

int test_omp_parallel_for_reduction() {
  int sum;
  int known_sum;
  int diff;
  int product;
  int known_product;
  int logic_and;
  int logic_or;
  int bit_and;
  int bit_or;
  int exclusiv_bit_or;
  int logics[LOOPCOUNT];
  int i;
  int result;

  sum = 0;
  result = 0;
  product = 1;
  logic_and = 1;
  logic_or = 0;
  bit_and = 1;
  bit_or = 0;
  exclusiv_bit_or = 0;

  /* Tests for integers */
  known_sum = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;
#pragma omp parallel for schedule(static, 1) private(i) reduction(+ : sum)
  for (i = 1; i <= LOOPCOUNT; i++) {
    sum = sum + i;
  }
  if (known_sum != sum) {
    result++;
    printf("Error in sum with integers: Result was %d"
           " instead of %d\n",
           sum, known_sum);
  }

  diff = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;
#pragma omp parallel for schedule(static, 1) private(i) reduction(- : diff)
  for (i = 1; i <= LOOPCOUNT; ++i) {
    diff = diff - i;
  }
  if (diff != 0) {
    result++;
    printf("Error in difference with integers: Result was %d"
           " instead of 0.\n",
           diff);
  }

/* Tests for integers */
#pragma omp parallel for schedule(static, 1) private(i) reduction(* : product)
  for (i = 1; i <= MAX_FACTOR; i++) {
    product *= i;
  }
  known_product = KNOWN_PRODUCT;
  if (known_product != product) {
    result++;
    printf("Error in Product with integers: Result was %d"
           " instead of %d\n\n",
           product, known_product);
  }

  /* Tests for logic AND */
  for (i = 0; i < LOOPCOUNT; i++) {
    logics[i] = 1;
  }

#pragma omp parallel for private(i) schedule(static,1) reduction(&&:logic_and)
  for (i = 0; i < LOOPCOUNT; ++i) {
    logic_and = (logic_and && logics[i]);
  }
  if (!logic_and) {
    result++;
    printf("Error in logic AND part 1.\n");
  }

  logic_and = 1;
  logics[LOOPCOUNT / 2] = 0;

#pragma omp parallel for schedule(static,1) private(i) reduction(&&:logic_and)
  for (i = 0; i < LOOPCOUNT; ++i) {
    logic_and = logic_and && logics[i];
  }
  if (logic_and) {
    result++;
    printf("Error in logic AND part 2.\n");
  }

  /* Tests for logic OR */
  for (i = 0; i < LOOPCOUNT; i++) {
    logics[i] = 0;
  }

#pragma omp parallel for schedule(static, 1) private(i) reduction(|| : logic_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    logic_or = logic_or || logics[i];
  }
  if (logic_or) {
    result++;
    printf("Error in logic OR part 1.\n");
  }
  logic_or = 0;
  logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static, 1) private(i) reduction(|| : logic_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    logic_or = logic_or || logics[i];
  }
  if (!logic_or) {
    result++;
    printf("Error in logic OR part 2.\n");
  }

  /* Tests for bitwise AND */
  for (i = 0; i < LOOPCOUNT; ++i) {
    logics[i] = 1;
  }

#pragma omp parallel for schedule(static, 1) private(i) reduction(& : bit_and)
  for (i = 0; i < LOOPCOUNT; ++i) {
    bit_and = (bit_and & logics[i]);
  }
  if (!bit_and) {
    result++;
    printf("Error in BIT AND part 1.\n");
  }

  bit_and = 1;
  logics[LOOPCOUNT / 2] = 0;

#pragma omp parallel for schedule(static, 1) private(i) reduction(& : bit_and)
  for (i = 0; i < LOOPCOUNT; ++i) {
    bit_and = bit_and & logics[i];
  }
  if (bit_and) {
    result++;
    printf("Error in BIT AND part 2.\n");
  }

  /* Tests for bitwise OR */
  for (i = 0; i < LOOPCOUNT; i++) {
    logics[i] = 0;
  }

#pragma omp parallel for schedule(static, 1) private(i) reduction(| : bit_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    bit_or = bit_or | logics[i];
  }
  if (bit_or) {
    result++;
    printf("Error in BIT OR part 1\n");
  }
  bit_or = 0;
  logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static, 1) private(i) reduction(| : bit_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    bit_or = bit_or | logics[i];
  }
  if (!bit_or) {
    result++;
    printf("Error in BIT OR part 2\n");
  }

  /* Tests for bitwise XOR */
  for (i = 0; i < LOOPCOUNT; i++) {
    logics[i] = 0;
  }

#pragma omp parallel for schedule(static,1) private(i) reduction(^:exclusiv_bit_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
  }
  if (exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 1\n");
  }

  exclusiv_bit_or = 0;
  logics[LOOPCOUNT / 2] = 1;

#pragma omp parallel for schedule(static,1) private(i) reduction(^:exclusiv_bit_or)
  for (i = 0; i < LOOPCOUNT; ++i) {
    exclusiv_bit_or = exclusiv_bit_or ^ logics[i];
  }
  if (!exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 2\n");
  }
  return (result);
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  int i;
  int num_failed = 0;

  if (core_id == 0) {
    printf("Master Thread start\n");
    for (i = 0; i < REPETITIONS; i++) {
      printf("test: %d\n", i);
      num_failed = test_omp_parallel_for_reduction();
      printf("num_failed: %d\n", num_failed);
    }
    printf("Master Thread end\n\n\n");
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return num_failed;
}
