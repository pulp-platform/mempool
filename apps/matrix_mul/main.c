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

#include "printf.h"
#include <stdint.h>
#include <string.h>
#include "encoding.h"

#define N 64
#define M 64
// #define VERBOSE

volatile uint32_t atomic __attribute__ ((section (".l1")));
volatile uint32_t a[N][M] __attribute__ ((section (".l1")));
volatile uint32_t b[M][N] __attribute__ ((section (".l1")));
volatile uint32_t c[N][N] __attribute__ ((section (".l1")));

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

void matrix_multiplication(uint32_t coreid, uint32_t num_cores) {
  asm volatile ("nop"::);
  uint32_t sum;
  for (int i=coreid; i<N; i += num_cores) {
    for (int j=0; j<N; j++) {
      sum = 0;
      for (int k=0; k<M; k++) {
        sum += a[i][k] * b[k][j];
      }
      c[i][j] = sum;
    }
  }
  asm volatile ("nop"::);
}

void matrix_multiplication_unrolled(uint32_t coreid, uint32_t num_cores) {
  asm volatile ("nop"::);
  for (int i=coreid; i<N; i += num_cores) {
    uint32_t sum0 = 0;
    uint32_t sum1 = 0;
    uint32_t sum2 = 0;
    uint32_t sum3 = 0;
    for (int j=0; j<N; j += 4) {
      for (int k=0; k<M; k++) {
        uint32_t val_a  = a[i][k];
        uint32_t val_b0 = b[k][j+0];
        uint32_t val_b1 = b[k][j+1];
        uint32_t val_b2 = b[k][j+2];
        uint32_t val_b3 = b[k][j+3];
        sum0 += val_a * val_b0;
        sum1 += val_a * val_b1;
        sum2 += val_a * val_b2;
        sum3 += val_a * val_b3;
      }
      c[i][j+0] = sum0;
      c[i][j+1] = sum1;
      c[i][j+2] = sum2;
      c[i][j+3] = sum3;
    }
  }
  asm volatile ("nop"::);
}

void barrier(uint32_t coreid, uint32_t num_cores) {
  while (atomic % num_cores != coreid);
  atomic = coreid+1;
  while (atomic != num_cores);
}

int main(uint32_t coreid, uint32_t num_cores) {
  //TODO(sriedel): This is a hack, to be fixed when MemPool has a fence mechanism.
  atomic = 0;

// #ifdef VERBOSE
  if (coreid == 0) {
    printf("Initialize\n");
  }
// #endif

  // Initialize a and b
  for (int i=coreid; i<N; i += num_cores) {
    for (int j=0; j<M; j++) {
      a[i][j] = coreid+i+j;
      b[j][i] = i*coreid+j;
    }
  }

  barrier(coreid, num_cores);

#ifdef VERBOSE
  if (coreid == 0) {
    printf("A:\n");

    for (int i=0; i<N; i++) {
      for (int j=0; j<M; j++) {
        printf("%4u ", a[i][j]);
      }
      printf("\n");
    }

    printf("B:\n");
    for (int j=0; j<M; j++) {
      for (int i=0; i<N; i++) {
        printf("%4u ", b[j][i]);
      }
      printf("\n");
    }
  }

  barrier(coreid, num_cores);

  if (coreid == 0) {
    printf("Start\n");
  }
#endif

  // Matrices are initialized --> Start calculating
  matrix_multiplication_unrolled(coreid, num_cores);

#ifdef VERBOSE
  if (coreid == 0) {
    printf("Done\n");
  }
#endif

  // wait until all cores have finished
  barrier(coreid, num_cores);

#ifdef VERBOSE
  if (coreid == 0) {
    printf("Print:\n");

    for (int i=0; i<N; i++) {
      for (int j=0; j<N; j++) {
        printf("%4u ", c[i][j]);
      }
      printf("\n");
    }
  }

  barrier(coreid, num_cores);
#endif

  return 0;
}
