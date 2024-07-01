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

#define MAX_BARRIERS 16

int main() {
#pragma omp parallel
  {
    unsigned int counter = 0;
    unsigned int cycles = 0;
    unsigned int start_time = 0;

    for (int i = 1; i < MAX_BARRIERS + 1; i++) {

      start_time = mempool_get_timer();
      mempool_start_benchmark();

      for (int j = 0; j < i; j++) {
#pragma omp barrier
        counter++;
      }

      mempool_stop_benchmark();
      cycles = mempool_get_timer() - start_time;

#pragma omp single
      printf("%d barriers: %d cycles\n", i, cycles);
    }
  }

  return 0;
}
