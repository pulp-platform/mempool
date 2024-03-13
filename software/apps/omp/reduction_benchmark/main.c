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

// Define Vector dimensions:
// C = AB with A=[Mx1], B=[Mx1]
#define M (NUM_CORES * 10)
// Specify how the vectors A and B should be initialized
// The entries will follow this format:
// a(i) = A_a*i + A_b
// b(i) = B_a*i + B_b
// The result will be the following
// c = (A_b*B_b) * N
//     + (A_a*B_b+A_b*B_a) * (N*(N-1))/2
//     + (A_a*B_a) * (N*(N-1)*(2*N-1))/6
// Note: To keep the code simpler, we use indices that go from 0 to N-1 instead
// of 1 to N as the mathematicians do. Hence, for A, i=[0,M-1].
#define A_a 1
#define A_b 1
#define B_a 1
#define B_b -1
// Enable verbose printing
#define VERBOSE

int32_t volatile init __attribute__((section(".l2"))) = 0;
int32_t a[M] __attribute__((section(".l1")));
int32_t b[M] __attribute__((section(".l1")));
int32_t c[NUM_CORES] __attribute__((section(".l1")));

// Initialize the matrices in parallel
void init_vector(int32_t *vector, uint32_t num_elements, int32_t a, int32_t b,
                 uint32_t core_id, uint32_t num_cores) {
  // Parallelize over rows
  for (uint32_t i = core_id; i < num_elements; i += num_cores) {
    vector[i] = a * (int32_t)i + b;
  }
}

void print_vector(int32_t const *vector, uint32_t num_elements) {
  printf("0x%8X\n", (uint32_t)vector);
  for (uint32_t i = 0; i < num_elements; ++i) {
    printf("%5d ", vector[i]);
    printf("\n");
  }
}

// Initialize the matrices in parallel
int verify_dotproduct(int32_t dotp, uint32_t num_elements, int32_t aa,
                      int32_t ab, int32_t ba, int32_t bb, int32_t *golden) {
  int32_t N = (int32_t)num_elements;
  *golden = aa * ba * N * (N - 1) * (2 * N - 1) / 6 +
            (aa * bb + ab * ba) * N * (N - 1) / 2 + ab * bb * (N);
  if (dotp == *golden)
    return 1;
  return 0;
}

int32_t dot_product_sequential(int32_t const *__restrict__ A,
                               int32_t const *__restrict__ B,
                               uint32_t num_elements) {
  uint32_t i;
  int32_t dotp = 0;
  for (i = 0; i < num_elements; i++) {
    dotp += A[i] * B[i];
  }
  return dotp;
}

int32_t dot_product_parallel1(int32_t const *__restrict__ A,
                              int32_t const *__restrict__ B,
                              int32_t *__restrict__ Partial_sums,
                              uint32_t num_elements, uint32_t id,
                              uint32_t numThreads) {

  Partial_sums[id] = 0;
  int32_t dotp = 0;
  for (uint32_t i = id; i < num_elements; i += numThreads) {
    Partial_sums[id] += A[i] * B[i];
  }
  mempool_barrier(numThreads);
  if (id == 0) {
    for (uint32_t i = 0; i < numThreads; i += 1) {
      dotp += Partial_sums[i];
    }
  }
  mempool_barrier(numThreads);
  return dotp;
}

int32_t dot_product_parallel2(int32_t const *__restrict__ A,
                              int32_t const *__restrict__ B,
                              int32_t *__restrict__ Partial_sums,
                              uint32_t num_elements, uint32_t id,
                              uint32_t numThreads) {

  Partial_sums[id] = 0;
  int32_t dotp = 0;
  for (uint32_t i = id * num_elements / numThreads;
       i < (id + 1) * num_elements / numThreads; i += 1) {
    Partial_sums[id] += A[i] * B[i];
  }
  mempool_barrier(numThreads);
  if (id == 0) {
    for (uint32_t i = 0; i < numThreads; i += 1) {
      dotp += Partial_sums[i];
    }
  }
  mempool_barrier(numThreads);
  return dotp;
}

int32_t dot_product_omp_static(int32_t const *__restrict__ A,
                               int32_t const *__restrict__ B,
                               uint32_t num_elements) {
  uint32_t i;
  int32_t dotp = 0;
#pragma omp parallel for reduction(+ : dotp)
  for (i = 0; i < num_elements; i++) {
    dotp += A[i] * B[i];
  }
  return dotp;
}

int32_t dot_product_omp_dynamic(int32_t const *__restrict__ A,
                                int32_t const *__restrict__ B,
                                uint32_t num_elements, uint32_t chunksize) {
  uint32_t i;
  int32_t dotp = 0;
  // printf("num_elements %d\n", num_elements);
#pragma omp parallel for schedule(dynamic, chunksize) reduction(+ : dotp)
  for (i = 0; i < num_elements; i++) {
    dotp += A[i] * B[i];
  }
  return dotp;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_timer_t cycles;

  // Initialize synchronization variables
  mempool_barrier_init(core_id);

#ifdef VERBOSE
  if (core_id == 0) {
    printf("Initialize\n");
  }
#endif

  // Initialize Matrices
  init_vector(a, M, A_a, A_b, core_id, num_cores);
  init_vector(b, M, B_a, B_b, core_id, num_cores);

#ifdef VERBOSE
  mempool_barrier(num_cores);
  if (core_id == 0) {
    // print_vector(a, M);
    // print_vector(b, M);
  }
#endif

  mempool_barrier(num_cores);
  int32_t result, correct_result;

  if (core_id == 0) {
    mempool_wait(4 * num_cores);
    cycles = mempool_get_timer();
    mempool_start_benchmark();
    result = dot_product_sequential(a, b, M);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;
  }

#ifdef VERBOSE
  mempool_barrier(num_cores);
  if (core_id == 0) {
    printf("Sequential Result: %d\n", result);
    printf("Sequential Duration: %d\n", cycles);
    if (!verify_dotproduct(result, M, A_a, A_b, B_a, B_b, &correct_result)) {
      printf("Sequential Result is %d instead of %d\n", result, correct_result);
    } else {
      printf("Result is correct!\n");
    }
  }
#endif
  mempool_barrier(num_cores);

  cycles = mempool_get_timer();
  mempool_start_benchmark();
  result = dot_product_parallel1(a, b, c, M, core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

#ifdef VERBOSE
  mempool_barrier(num_cores);
  if (core_id == 0) {
    printf("Manual Parallel1 Result: %d\n", result);
    printf("Manual Parallel1 Duration: %d\n", cycles);
    if (!verify_dotproduct(result, M, A_a, A_b, B_a, B_b, &correct_result)) {
      printf("Manual Parallel1 Result is %d instead of %d\n", result,
             correct_result);
    } else {
      printf("Result is correct!\n");
    }
  }
#endif
  mempool_barrier(num_cores);

  cycles = mempool_get_timer();
  mempool_start_benchmark();
  result = dot_product_parallel2(a, b, c, M, core_id, num_cores);
  mempool_stop_benchmark();
  cycles = mempool_get_timer() - cycles;

#ifdef VERBOSE
  mempool_barrier(num_cores);
  if (core_id == 0) {
    printf("Manual Parallel2 Result: %d\n", result);
    printf("Manual Parallel2 Duration: %d\n", cycles);
    if (!verify_dotproduct(result, M, A_a, A_b, B_a, B_b, &correct_result)) {
      printf("Manual Parallel2 Result is %d instead of %d\n", result,
             correct_result);
    } else {
      printf("Result is correct!\n");
    }
  }
#endif
  mempool_barrier(num_cores);

  /*  OPENMP IMPLEMENTATION  */
  int32_t omp_result;

  if (core_id == 0) {
    mempool_wait(4 * num_cores);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    omp_result = dot_product_omp_static(a, b, M);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    printf("OMP Static Result: %d\n", omp_result);
    printf("OMP Static Duration: %d\n", cycles);
    if (!verify_dotproduct(omp_result, M, A_a, A_b, B_a, B_b,
                           &correct_result)) {
      printf("OMP Static Result is %d instead of %d\n", omp_result,
             correct_result);
    } else {
      printf("Result is correct!\n");
    }

    mempool_wait(4 * num_cores);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    omp_result = dot_product_omp_dynamic(a, b, M, 4);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    printf("OMP Dynamic(4) Result: %d\n", omp_result);
    printf("OMP Dynamic(4) Duration: %d\n", cycles);
    if (!verify_dotproduct(omp_result, M, A_a, A_b, B_a, B_b,
                           &correct_result)) {
      printf("OMP Dynamic(4) Result is %d instead of %d\n", omp_result,
             correct_result);
    } else {
      printf("Result is correct!\n");
    }

    mempool_wait(4 * num_cores);

    cycles = mempool_get_timer();
    mempool_start_benchmark();
    omp_result = dot_product_omp_dynamic(a, b, M, 10);
    mempool_stop_benchmark();
    cycles = mempool_get_timer() - cycles;

    printf("OMP Dynamic(10) Result: %d\n", omp_result);
    printf("OMP Dynamic(10) Duration: %d\n", cycles);
    if (!verify_dotproduct(omp_result, M, A_a, A_b, B_a, B_b,
                           &correct_result)) {
      printf("OMP Dynamic(10) Result is %d instead of %d\n", omp_result,
             correct_result);
    } else {
      printf("Result is correct!\n");
    }

    mempool_wait(4 * num_cores);

  } else {
    while (1) {
      mempool_wfi();
      run_task(core_id);
    }
  }
  return 0;
}
