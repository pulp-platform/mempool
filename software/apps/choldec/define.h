// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define N_BANKS (NUM_CORES * 4)

/* Dimension of the input matrix */
#define N 4

/* TEST1 Single-Core Colesky decomposition --> #define SINGLE
   TEST2 Single-Core system inversion --> #define SINGLE #define LINSOLVER
   TEST3 Parallel Cholesky decomposition --> #define PARALLEL
   TEST4 Parallel folded Cholesky decomposition --> #define FOLDED
   TEST5 Parallel folded system inversion --> #define FOLDED LINSOLVER */

//#define SINGLE
//#define PARALLEL
//#define FOLDED
//#define LINSOLVER

/* All the versions follow Crout algorithm. For the single-core version
   Banachievitz is implemented too. #define BANACHIEWITZ or #define CROUT*/
#define CROUT

/* Define VERBOSE to see the matrix printed. */
#define VERBOSE

/* DATA */

int32_t A_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t AT_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t M_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
int32_t In[N] __attribute__((aligned(N_BANKS), section(".l1")));

int32_t LL_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));
int32_t LR_matrix[N * N_BANKS]
    __attribute__((aligned(N_BANKS), section(".l1")));

int32_t L_matrix[N * N] __attribute__((aligned(N_BANKS), section(".l1")));
