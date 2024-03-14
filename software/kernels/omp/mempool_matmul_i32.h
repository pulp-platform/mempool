// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the matrix multiplication in multiple different ways.
 * The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 */

// OpenMP Implementations
#ifdef _OPENMP

void mat_mul_parallel_omp(int32_t const *__restrict__ A,
                          int32_t const *__restrict__ B,
                          int32_t *__restrict__ C, uint32_t M, uint32_t N,
                          uint32_t P) {
#pragma omp parallel for
  for (uint32_t i = 0; i < M; i++) {
    for (uint32_t j = 0; j < P; ++j) {
      int32_t c = 0;
      for (uint32_t k = 0; k < N; ++k) {
        c += A[i * N + k] * B[k * P + j];
      }
      C[i * P + j] = c;
    }
  }
}

void mat_mul_unrolled_parallel_omp(int32_t const *__restrict__ A,
                                   int32_t const *__restrict__ B,
                                   int32_t *__restrict__ C, uint32_t M,
                                   uint32_t N, uint32_t P) {
// Parallelize by assigning each core one row
#pragma omp parallel for
  for (uint32_t i = 0; i < M; i++) {
    for (uint32_t j = 0; j < P; j += 4) {
      int32_t c0 = 0;
      int32_t c1 = 0;
      int32_t c2 = 0;
      int32_t c3 = 0;
      for (uint32_t k = 0; k < N; ++k) {
        // Explicitly load the values first to help with scheduling
        int32_t val_a = A[i * N + k];
        int32_t val_b0 = B[k * P + j + 0];
        int32_t val_b1 = B[k * P + j + 1];
        int32_t val_b2 = B[k * P + j + 2];
        int32_t val_b3 = B[k * P + j + 3];
        c0 += val_a * val_b0;
        c1 += val_a * val_b1;
        c2 += val_a * val_b2;
        c3 += val_a * val_b3;
      }
      C[i * P + j + 0] = c0;
      C[i * P + j + 1] = c1;
      C[i * P + j + 2] = c2;
      C[i * P + j + 3] = c3;
    }
  }
}

#endif
