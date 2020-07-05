// Copyright 2020 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "../common/kernel/mat_mul.h"
#include "../common/runtime.h"
#include "../common/synchronization.h"
#include "encoding.h"
// #include "kernel/mat_mul.h"
#include "printf.h"

#define M 12
#define N 8
#define P 4
#define VERBOSE

volatile uint32_t init __attribute__((section(".data"))) = 0;
volatile uint32_t a[M][N] __attribute__((section(".l1")));
volatile uint32_t b[N][P] __attribute__((section(".l1")));
volatile uint32_t c[M][P] __attribute__((section(".l1")));

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

void matrix_multiplication(uint32_t coreid, uint32_t num_cores) {
  asm volatile("nop" ::);
  uint32_t sum;
  for (int i = coreid; i < N; i += num_cores) {
    for (int j = 0; j < N; j++) {
      sum = 0;
      for (int k = 0; k < M; k++) {
        sum += a[i][k] * b[k][j];
      }
      c[i][j] = sum;
    }
  }
  asm volatile("nop" ::);
}

void matrix_multiplication_unrolled(uint32_t coreid, uint32_t num_cores) {
  asm volatile("nop" ::);
  for (int i = coreid; i < N; i += num_cores) {
    uint32_t sum0 = 0;
    uint32_t sum1 = 0;
    uint32_t sum2 = 0;
    uint32_t sum3 = 0;
    for (int j = 0; j < N; j += 4) {
      for (int k = 0; k < M; k++) {
        uint32_t val_a = a[i][k];
        uint32_t val_b0 = b[k][j + 0];
        uint32_t val_b1 = b[k][j + 1];
        uint32_t val_b2 = b[k][j + 2];
        uint32_t val_b3 = b[k][j + 3];
        sum0 += val_a * val_b0;
        sum1 += val_a * val_b1;
        sum2 += val_a * val_b2;
        sum3 += val_a * val_b3;
      }
      c[i][j + 0] = sum0;
      c[i][j + 1] = sum1;
      c[i][j + 2] = sum2;
      c[i][j + 3] = sum3;
    }
  }
  asm volatile("nop" ::);
}

int main(int argc, char **argv) {
  uint32_t coreid = (uint32_t)argc;
  uint32_t num_cores = (uint32_t)argv;

  // Initialize synchronization variables
  if (coreid == 0) {
    mempool_barrier_init();
    init = 1;
  } else {
    // FIXME: The other cores can not see changes introduced by the master core
    // to the L2 memory
    // while (!init) {
    mempool_wait(2000);
    // }
  }

  // #ifdef VERBOSE
  if (coreid == 0) {
    printf("Initialize\n");
  }
  // #endif

  // Initialize a
  for (int i = coreid; i < M; i += num_cores) {
    for (int j = 0; j < N; j++) {
      a[i][j] = coreid + i + j;
    }
  }
  // Initialize b
  for (int i = coreid; i < N; i += num_cores) {
    for (int j = 0; j < P; j++) {
      b[i][j] = i * coreid + j;
    }
  }

  mempool_barrier(coreid, num_cores);

#ifdef VERBOSE
  if (coreid == 0) {
    printf("A:\n");

    for (int i = 0; i < M; i++) {
      for (int j = 0; j < N; j++) {
        printf("%4u ", a[i][j]);
      }
      printf("\n");
    }

    printf("B:\n");
    for (int j = 0; j < N; j++) {
      for (int i = 0; i < P; i++) {
        printf("%4u ", b[i][j]);
      }
      printf("\n");
    }
    printf("Start\n");
  }

  mempool_barrier(coreid, num_cores);
#endif

  // Matrices are initialized --> Start calculating
  asm volatile("nop" ::);
  mat_mul_parallel(a, b, c, M, N, P, coreid, num_cores);
  asm volatile("nop" ::);

  // Check result
  if (coreid == 0) {
    int error = check_mat_mul(a, b, c, M, N, P);
    if (error != 0) {
      printf("Error in Matrix Multiplication\n");
    }
#ifdef VERBOSE
    printf("Done\n");
#endif
  }

  // wait until all cores have finished
  mempool_barrier(coreid, num_cores);

#ifdef VERBOSE
  if (coreid == 0) {
    printf("Print:\n");

    for (int i = 0; i < M; i++) {
      for (int j = 0; j < P; j++) {
        printf("%4u ", c[i][j]);
      }
      printf("\n");
    }
  }

  mempool_barrier(coreid, num_cores);
#endif

  return 0;
}
