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

void mat_mul_sequential(int32_t const *__restrict__ A,
                        int32_t const *__restrict__ B, int32_t *__restrict__ C,
                        uint32_t M, uint32_t N, uint32_t P) {
  // Parallelize by assigning each core one row
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
