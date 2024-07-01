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

#define N 16
#define M 4

uint32_t work2(unsigned long num) {
  uint32_t i;
  uint32_t cnt = 0;

  for (i = 0; i < num; i++)
    cnt += i;

  return cnt;
}

void sequential() {
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void static_parallel() {
#pragma omp parallel for num_threads(4)
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void dynamic_parallel() {
#pragma omp parallel for num_threads(4) schedule(dynamic, M)
  for (int i = 0; i < N; i++) {
    work2(100);
  }
}

void section_parallel() {
#pragma omp parallel num_threads(4)
  {
#pragma omp sections
    {
#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }

#pragma omp section
      {
        for (int i = 0; i < M; i++) {
          work2(100);
        }
      }
    }
  }
}

#define REPETITIONS 10

void startup_time() {

  uint32_t duration = 0;

  for (int i = 0; i < REPETITIONS; i++) {
    uint32_t time = mempool_get_timer();
#pragma omp parallel
    {
#pragma omp single
      duration += mempool_get_timer() - time;
    }
  }

  printf("Startup time duration: %d\n", duration / REPETITIONS);
}

int main() {
  uint32_t cycles;

  printf("Sequential Start\n");
  cycles = mempool_get_timer();
  mempool_start_benchmark();
  sequential();
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  printf("Sequential Duration: %d\n", cycles);

  printf("Static Start\n");
  cycles = mempool_get_timer();
  mempool_start_benchmark();
  static_parallel();
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  printf("Static Duration: %d\n", cycles);

  printf("Dynamic Start\n");
  cycles = mempool_get_timer();
  mempool_start_benchmark();
  dynamic_parallel();
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  printf("Dynamic Duration: %d\n", cycles);

  printf("Section Start\n");
  cycles = mempool_get_timer();
  mempool_start_benchmark();
  section_parallel();
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;
  printf("Section Duration: %d\n", cycles);

  startup_time();

  return 0;
}
