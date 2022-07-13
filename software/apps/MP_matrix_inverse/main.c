// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

//#include <stdint.h>
//#include <string.h>

#define N 5

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "inverse.h"
#include "initialization.h"

// C++ program to find Moore-Penrose inverse  matrix
 
// Generic function to display the matrix. We use it to display
// both adjoin and inverse. adjoin is integer matrix and inverse
// is a int32_t.
void display(int32_t *A, int32_t n)
{
    for (int i = 0; i < n; i++)
    {
        for (int j = 0; j < n; j++)
            printf("%4d ", A[i * n + j]);
        printf("\n");
    }
}

// Driver program
int main()
{

    uint32_t core_id = mempool_get_core_id();
    uint32_t num_cores = mempool_get_core_count();
    // Initialize barrier and synchronize
    mempool_barrier_init(core_id);

    int32_t matrix[N * N] = {  -2, 2, 7, 9, 4, 0, 8,
                                1, 0, 0, 3, 1, 0, 9,
                               -3, 1, 5, 0, 2, 1, 7,
                                3,-1,-9, 4, 6, 5, 2,
                                1, 0, 4, 4, 1, 0, 9,
                                8, 0, 3, 8, 6, 5, 2,
                                5, 6, 4, 1, 3, 2, 0  };

    int32_t t_matrix[N * N];
    int32_t matrix_mult[N * N];
    int32_t pseudoinverse[N * N];
    int32_t inv[N * N]; // To store inverse 

//    init_matrix_zeros(t_matrix, N, N, core_id, num_cores);
//    init_matrix_zeros(matrix_mult, N, N, core_id, num_cores);
//    init_matrix_zeros(pseudoinverse, N, N, core_id, num_cores);
//    init_matrix_zeros(adj, N, N, core_id, num_cores);
//    init_matrix_zeros(inv, N, N, core_id, num_cores);
    if(core_id == 0)
      display(matrix, N);

    if(core_id == 0) {
      Transpose(matrix, t_matrix, N);
      printf("\nThe Transpose is :\n");
      display(t_matrix, N);
      printf("The product of the matrix is: \n");
      MatrixMult(t_matrix,matrix,matrix_mult, N);
      display(matrix_mult, N);
      printf("\nThe Inverse is :\n");
      if (inverse(matrix_mult, inv, N))
          display(inv, N);
      MatrixMult(inv,t_matrix,pseudoinverse, N);
      printf("\nThe Monroe-penrose inverse is :\n");
      display(pseudoinverse, N);
    }

    mempool_barrier(num_cores);
    return 0;
}
