// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

//#include <stdint.h>
//#include <string.h>

#define N 16
#define M 16
#define O 16
#define N_BANKS (1024)

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_mat_inv_q32p.h"
#include "mempool_mat_inv_q32p_memsized.h"
#include "mempool_mat_inv_q32s.h"


#define VERBOSE
// #define SINGLE
// #define PARALLEL
#define MEMSIZED

int32_t matrix[N * M]         __attribute__((aligned(N), section(".l1")));
int32_t inv[M * M]            __attribute__((aligned(N), section(".l1")));
uint32_t flag                 __attribute__((section(".l1")));

void display(int32_t *A, int32_t n, int32_t m) {
    //int32_t i, j;
    //for (i = 0; i < n; i++) {
    //  for (j = 0; j < m; j++) {
    //    printf("%8d ", A[i * m + j]);
    //  }
    //  printf("\n");
    //}
    int32_t i;
    for (i = 0; i < n * m; i++) {
      printf("Output[%d] = %8d\n", i, A[i]);
    }
}

// Driver program
void single_core()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    init_matrix(matrix, N, M, -156, 427, -219, core_id);
    init_matrix_zeros(inv, M, M, core_id);
    mempool_barrier(num_cores);

    if(core_id == 0) {
        mempool_start_benchmark();
        mempool_GJinv_q32s(matrix, inv, M);
        mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
    #ifdef VERBOSE
    if (core_id == 0)
      display(inv, N, M);
    #endif
    mempool_barrier(num_cores);
}

void multi_core()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    init_matrix(matrix, N, M, -156, 427, -219, core_id);
    init_matrix_zeros(inv, M, M, core_id);
    if (core_id == 0) {
        flag = 0U;
    }
    mempool_barrier(num_cores);

    if (core_id < MIN(NUM_CORES, N / 4)) {
      mempool_start_benchmark();
      mempool_GJinv_q32p(matrix, inv, M, &flag);
      mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
    #ifdef VERBOSE
    if (core_id == 0)
      display(inv, M, N);
    #endif
    mempool_barrier(num_cores);
}

void multi_core_memsized()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    init_matrix(matrix, N, M, -156, 427, -219, core_id);
    init_matrix_zeros(inv, M, M, core_id);
    if (core_id == 0) {
        flag = 0U;
    }
    mempool_barrier(num_cores);

    mempool_start_benchmark();
    mempool_GJinv_q32p_memsized(matrix, inv, M, &flag);
    mempool_stop_benchmark();

    mempool_barrier(num_cores);
    #ifdef VERBOSE
    if (core_id == 0)
      display(inv, M, N);
    #endif
    mempool_barrier(num_cores);
}

int main() {
    #if defined(SINGLE)
    single_core();
    #elif defined(PARALLEL)
    multi_core();
    #elif defined(MEMSIZED)
    multi_core_memsized();
    #endif
    return 0;
}
