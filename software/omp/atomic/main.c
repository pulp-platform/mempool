// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "libgomp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define REPETITIONS 10 /* Number of times to run each test */
#define MAX_FACTOR 10
#define KNOWN_PRODUCT 3628800 /* 10! */
#define LOOPCOUNT 100         /* Number of iterations to slit amongst threads */

int test_omp_atomic() {
  int sum;
  int diff;
  int product;
  int x;
  int *logics;
  int bit_and = 1;
  int bit_or = 0;
  int exclusiv_bit_or = 0;
  int j;
  int known_sum;
  int known_diff;
  int known_product;
  int result = 0;
  int logicsArray[LOOPCOUNT];
  logics = logicsArray;

  sum = 0;
  diff = 0;
  product = 1;

// sum of integers test
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 1; i <= LOOPCOUNT; i++) {
#pragma omp atomic
      sum += i;
    }
  }
  known_sum = (LOOPCOUNT * (LOOPCOUNT + 1)) / 2;
  if (known_sum != sum) {
    printf("Error in sum with integers: Result was %d instead of %d.\n", sum,
           known_sum);
    result++;
  }

// difference of integers test
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; i++) {
#pragma omp atomic
      diff -= i;
    }
  }
  known_diff = ((LOOPCOUNT - 1) * LOOPCOUNT) / 2 * -1;
  if (diff != known_diff) {
    printf("Error in difference with integers: Result was %d instead of 0.\n",
           diff);
    result++;
  }

// product of integers test
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 1; i <= MAX_FACTOR; i++) {
#pragma omp atomic
      product *= i;
    }
  }
  known_product = KNOWN_PRODUCT;
  if (known_product != product) {
    printf("Error in product with integers: Result was %d instead of %d\n",
           product, known_product);
    result++;
  }

  // division of integers test
  product = KNOWN_PRODUCT;
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 1; i <= MAX_FACTOR; ++i) {
#pragma omp atomic
      product /= i;
    }
  }
  if (product != 1) {
    printf("Error in product division with integers: Result was %d"
           " instead of 1\n",
           product);
    result++;
  }

  // ++ test
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
  if (x != LOOPCOUNT) {
    result++;
    printf("Error in ++\n");
  }

// -- test
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      x--;
    }
  }
  if (x != 0) {
    result++;
    printf("Error in --\n");
  }

  // bit-and test part 1
  for (j = 0; j < LOOPCOUNT; ++j) {
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
  if (!bit_and) {
    result++;
    printf("Error in BIT AND part 1\n");
  }

  // bit-and test part 2
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
  if (bit_and) {
    result++;
    printf("Error in BIT AND part 2\n");
  }

  // bit-or test part 1
  for (j = 0; j < LOOPCOUNT; j++) {
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
  if (bit_or) {
    result++;
    printf("Error in BIT OR part 1\n");
  }

  // bit-or test part 2
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
  if (!bit_or) {
    result++;
    printf("Error in BIT OR part 2\n");
  }

  // bit-xor test part 1
  for (j = 0; j < LOOPCOUNT; j++) {
    logics[j] = 0;
  }
  exclusiv_bit_or = 0;
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < LOOPCOUNT; ++i) {
#pragma omp atomic
      exclusiv_bit_or ^= logics[i];
    }
  }
  if (exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 1\n");
  }

  // bit-xor test part 2
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
  if (!exclusiv_bit_or) {
    result++;
    printf("Error in EXCLUSIV BIT OR part 2\n");
  }

  // left shift test
  x = 1;
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < 10; ++i) {
#pragma omp atomic
      x <<= 1;
    }
  }
  if (x != 1024) {
    result++;
    printf("Error in <<\n");
    x = 1024;
  }

// right shift test
#pragma omp parallel
  {
    int i;
#pragma omp for
    for (i = 0; i < 10; ++i) {
#pragma omp atomic
      x >>= 1;
    }
  }
  if (x != 1) {
    result++;
    printf("Error in >>\n");
  }

  return (result);
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  int i;
  int num_failed = 0;

  mempool_wait(4 * num_cores);

  if (core_id == 0) {
    printf("Master Thread start\n");
    for (i = 0; i < REPETITIONS; i++) {
      printf("test: %d\n", i);
      num_failed = test_omp_atomic();
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
