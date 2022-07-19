// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

//#include <stdint.h>
//#include <string.h>

#define N 4
#define M 4
#define O 4

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "initialization.h"
#include "mempool_mat_inv_q16s.h"
#include "mempool_mat_inv_q16p.h"

// #define VERBOSE
// #define SINGLE
#define PARALLEL

int32_t matrix[N * M]         __attribute__((section(".l1")));
int32_t t_matrix[M * N]       __attribute__((section(".l1")));
int32_t matrix_mult[M * M]    __attribute__((section(".l1")));
int32_t inv[M * M]            __attribute__((section(".l1")));
int32_t pseudoinverse[M * N]  __attribute__((section(".l1")));
uint32_t flag                __attribute__((section(".l1")));

void display(int32_t *A, int32_t n, int32_t m) {
    //int32_t volatile i = 0;
    //while (i < n * m) {
    //    // printf("ciao mamma\n");
    //    printf("Value %d: %d\n", i, A[i]);
    //    i++;
    //}
    int32_t i, j;
    for (i = 0; i < n; i++) {
      for (j = 0; j < m; j++) {
        printf("%5d ", A[i * m + j]);
      }
      printf("\n");
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
    //init_matrix_zeros(t_matrix, M, N, core_id);
    //init_matrix_zeros(matrix_mult, M, M, core_id);
    //init_matrix_zeros(inv, M, M, core_id);
    //init_matrix_zeros(pseudoinverse, M, N, core_id);
    mempool_barrier(num_cores);

    if(core_id == 0) {
      #if defined(VERBOSE)
          display(matrix, N, M);
          Transpose(matrix, t_matrix, N,  M);
          printf("\nThe Transpose is :\n");
          display(t_matrix, M, N);
          MatrixMult(t_matrix, matrix, matrix_mult, M, N, O);
          printf("The product of the matrix is: \n");
          display(matrix_mult, M, M);
          printf("\nThe Inverse is :\n");
          mempool_mat_inv_q16s(matrix_mult, inv, N);
          display(inv, N, N);
          MatrixMult(t_matrix, inv, pseudoinverse, M, N, N);
          printf("\nThe Moore-Penrose inverse is :\n");
          display(pseudoinverse, M, N);
      #else
          //Transpose(matrix, t_matrix, N, M);
          //MatrixMult(t_matrix, matrix, matrix_mult, M, N, O);

          mempool_start_benchmark();
          mempool_GJinv_q16s(matrix, inv, M);
          mempool_stop_benchmark();

          //MatrixMult(inv, t_matrix, pseudoinverse, M, M, N);
          //MatrixMult(pseudoinverse, matrix, inv, M, N, M);
      #endif
    }
    mempool_barrier(num_cores);
}

void multi_core()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    init_matrix(matrix, N, M, -156, 427, -219, core_id);
    if (core_id == 0) {
        flag = 0U;
    }
    //init_matrix_zeros(t_matrix, M, N, core_id);
    //init_matrix_zeros(matrix_mult, M, M, core_id);
    //init_matrix_zeros(inv, M, M, core_id);
    //init_matrix_zeros(pseudoinverse, M, N, core_id);
    mempool_barrier(num_cores);

    //Transpose(matrix, t_matrix, N, M);
    //MatrixMult(t_matrix, matrix, matrix_mult, M, N, O);

    mempool_start_benchmark();
    mempool_GJinv_q16p(matrix, inv, M, &flag);
    mempool_stop_benchmark();

    //MatrixMult(inv, t_matrix, pseudoinverse, M, M, N);
    //MatrixMult(pseudoinverse, matrix, inv, M, N, M);

    mempool_barrier(num_cores);
}

int main() {
    #if defined(SINGLE)
    single_core();
    #elif defined(PARALLEL)
    multi_core();
    #endif
    return 0;
}
