// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define N 16
#define M 16
#define O 16
#define N_BANKS (1024)
#define N_USED_BANKS (64)

#define VERBOSE
// #define SINGLE
// #define PARALLEL
#define MEMSIZED
// #define FOLDED

#include "initialization.h"
#include "mempool_mat_inv_q32s.h"
#include "mempool_mat_inv_q32p.h"
#include "mempool_mat_inv_q32p_memsized.h"
#include "mempool_mat_inv_q32p_folded.h"

#ifdef FOLDED
int32_t matrix[N * M]                                       __attribute__((aligned(N_BANKS), section(".l1")));
int32_t folded_matrix[N_BANKS * ((N * M) / N_USED_BANKS)]   __attribute__((aligned(N_BANKS), section(".l1")));
int32_t inv[N_BANKS * ((N * M) / N_USED_BANKS)]             __attribute__((aligned(N_BANKS), section(".l1")));
uint32_t flag                                               __attribute__((section(".l1")));
#else
int32_t matrix[N * M]         __attribute__((aligned(N), section(".l1")));
int32_t inv[M * M]            __attribute__((aligned(N), section(".l1")));
uint32_t flag                 __attribute__((section(".l1")));
#endif

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
    init_matrix_zeros(inv, N, M, core_id);
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

#ifdef FOLDED
void multi_core_folded()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    uint32_t nPE = N_USED_BANKS >> 2U;
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    init_matrix(matrix, N, M, -156, 427, -219, core_id);
    init_matrix_zeros(folded_matrix, ((N * M) / N_USED_BANKS), N_BANKS, core_id);
    init_matrix_zeros(inv, ((N * M) / N_USED_BANKS), N_BANKS, core_id);
    if (core_id == 0) {
        flag = 0U;
    }
    mempool_barrier(num_cores);

    mempool_start_benchmark();
    fold_matrix(matrix, folded_matrix, N);
    mempool_stop_benchmark();
    if(core_id < nPE) {
        mempool_start_benchmark();
        mempool_GJinv_q32p_folded(folded_matrix, inv, M, &flag, nPE);
        mempool_stop_benchmark();
    }
    mempool_barrier(num_cores);
    #ifdef VERBOSE
    if (core_id == 0)
      display_folded(inv, M, N);
    #endif
    mempool_barrier(num_cores);

}
#endif

int main() {
    #if defined(SINGLE)
    single_core();
    #elif defined(PARALLEL)
    multi_core();
    #elif defined(MEMSIZED)
    multi_core_memsized();
    #elif defined(FOLDED)
    multi_core_folded();
    #endif
    return 0;
}
