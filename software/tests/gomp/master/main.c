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

int test_omp_master() {
  uint32_t nthreads;
  int32_t executing_thread;
  // counts up the number of wrong thread no. for the master thread. (Must be 0)
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
  return ((nthreads == 1) && (executing_thread == 0) && (tid == 0));
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t i;
  uint32_t num_failed = 0;

  if (core_id == 0) {
    printf("Master Thread start\n");
    for (i = 0; i < REPETITIONS; i++) {
      if (!test_omp_master()) {
        num_failed++;
      }
    }
    printf("Master Thread end\n\n\n");
    printf("num_failed:%d\n", num_failed);
  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }

  return 0;
}
