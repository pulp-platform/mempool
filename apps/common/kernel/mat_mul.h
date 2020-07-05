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

/* This library implements the matrix multiplication in multiple different ways.
 * The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 */

int check_mat_mul(uint32_t const *__restrict__ A,
                  uint32_t const *__restrict__ B,
                  uint32_t const *__restrict__ C, uint32_t M, uint32_t N,
                  uint32_t P) {
  for (uint32_t i = 0; i < M; ++i) {
    for (uint32_t j = 0; j < P; ++j) {
      uint32_t sum = 0;
      for (uint32_t k = 0; k < N; ++k) {
        sum += A[i * N + k] * B[k * P + j];
      }
      if (C[i * P + j] != sum) {
        return -1;
      }
    }
  }
  return 0;
}

void mat_mul(uint32_t const *__restrict__ A, uint32_t const *__restrict__ B,
             uint32_t *__restrict__ C, uint32_t M, uint32_t N, uint32_t P) {
  for (uint32_t i = 0; i < M; ++i) {
    for (uint32_t j = 0; j < P; ++j) {
      uint32_t sum = 0;
      for (uint32_t k = 0; k < N; ++k) {
        sum += A[i * N + k] * B[k * P + j];
      }
      C[i * P + j] = sum;
    }
  }
}

inline void mat_mul_parallel(uint32_t const *__restrict__ A,
                             uint32_t const *__restrict__ B,
                             uint32_t *__restrict__ C, uint32_t M, uint32_t N,
                             uint32_t P, uint32_t id, uint32_t numThreads) {
  // Parallelize over outermost loop. --> This is inefficient for small
  // matrices.
  if (numThreads < M) {
    // Merge outer loops to balance the workload
    // NOTE: The modulo operation is extremely expensive with non power of two
    // numbers
    uint32_t chunks = (M * P + numThreads - 1) / numThreads;
    uint32_t start = id * chunks;
    uint32_t end = (id == numThreads - 1) ? M * P : start + chunks;
    uint32_t i = start / P;
    uint32_t j = start % P;
    for (uint32_t ij = start; ij < end; ++ij) {
      uint32_t sum = 0;
      for (uint32_t k = 0; k < N; ++k) {
        sum += A[i * N + k] * B[k * P + j];
      }
      C[ij] = sum;
      if (++j == P) {
        j = 0;
        i++;
      }
    }
  } else {
    for (uint32_t i = id; i < M; i += numThreads) {
      for (uint32_t j = 0; j < P; ++j) {
        uint32_t sum = 0;
        for (uint32_t k = 0; k < N; ++k) {
          sum += A[i * N + k] * B[k * P + j];
        }
        C[i * P + j] = sum;
      }
    }
  }
  return;
}
