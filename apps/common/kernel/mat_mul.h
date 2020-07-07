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

void mat_mul_parallel(int32_t const *__restrict__ A,
                      int32_t const *__restrict__ B, int32_t *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t id,
                      uint32_t numThreads) {
  // Parallelize by assigning each core one row
  for (uint32_t i = id; i < M; i += numThreads) {
    for (uint32_t j = 0; j < P; ++j) {
      int32_t c = 0;
      for (uint32_t k = 0; k < N; ++k) {
        c += A[i * N + k] * B[k * P + j];
      }
      C[i * P + j] = c;
    }
  }
}

void mat_mul_parallel_finegrained(int32_t const *__restrict__ A,
                                  int32_t const *__restrict__ B,
                                  int32_t *__restrict__ C, uint32_t M,
                                  uint32_t N, uint32_t P, uint32_t id,
                                  uint32_t numThreads) {
  // Merge outer loops to balance the workload
  uint32_t chunks = (M * P + numThreads - 1) / numThreads;
  uint32_t start = id * chunks;
  uint32_t end = (id == numThreads - 1) ? M * P : start + chunks;
  uint32_t i = start / P;
  uint32_t j = start % P;
  for (uint32_t ij = start; ij < end; ++ij) {
    int32_t c = 0;
    for (uint32_t k = 0; k < N; ++k) {
      c += A[i * N + k] * B[k * P + j];
    }
    C[ij] = c;
    if (++j == P) {
      j = 0;
      i++;
    }
  }
}

void mat_mul(int32_t const *__restrict__ A, int32_t const *__restrict__ B,
             int32_t *__restrict__ C, uint32_t M, uint32_t N, uint32_t P) {
  mat_mul_parallel(A, B, C, M, N, P, 0, 1);
}

void mat_mul_unrolled_parallel(int32_t const *__restrict__ A,
                               int32_t const *__restrict__ B,
                               int32_t *__restrict__ C, uint32_t M, uint32_t N,
                               uint32_t P, uint32_t id, uint32_t numThreads) {
  // Parallelize by assigning each core one row
  for (uint32_t i = id; i < M; i += numThreads) {
    for (uint32_t j = 0; j < P; j += 4) {
      int32_t c0 = 0;
      int32_t c1 = 0;
      int32_t c2 = 0;
      int32_t c3 = 0;
      for (int k = 0; k < N; ++k) {
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

void mat_mul_unrolled_parallel_finegrained(int32_t const *__restrict__ A,
                                           int32_t const *__restrict__ B,
                                           int32_t *__restrict__ C, uint32_t M,
                                           uint32_t N, uint32_t P, uint32_t id,
                                           uint32_t numThreads) {
  // Merge outer loops to balance the workload
  uint32_t chunks = (M * P + numThreads - 1) / numThreads;
  uint32_t start = id * chunks;
  uint32_t end = (id == numThreads - 1) ? M * P : start + chunks;
  uint32_t i = start / P;
  uint32_t j = start % P;
  for (uint32_t ij = start; ij < end; ij += 4) {
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
    C[ij + 0] = c0;
    C[ij + 1] = c1;
    C[ij + 2] = c2;
    C[ij + 3] = c3;
    // Increment j and increment i when wrapping j around
    if (j == P - 4) {
      j = 0;
      i++;
    } else {
      j += 4;
    }
  }
}

void mat_mul_unrolled(int32_t const *__restrict__ A,
                      int32_t const *__restrict__ B, int32_t *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P) {
  mat_mul_unrolled_parallel(A, B, C, M, N, P, 0, 1);
}

static inline void mat_mul_asm_parallel(int32_t const *__restrict__ A,
                                        int32_t const *__restrict__ B,
                                        int32_t *__restrict__ C, uint32_t M,
                                        uint32_t N, uint32_t P, uint32_t id,
                                        uint32_t numThreads) {
  // Do this loop M times
  for (int i = id; i < M; i += numThreads) {
    int32_t const *start_a = &A[i * N];
    int32_t const *end_a = &A[(i + 1) * N];
    int32_t const *start_b = &B[0];
    int32_t const *idx_b = &B[0];
    int32_t *start_c = &C[i * P];
    int32_t *end_c = &C[(i + 1) * P];
    // Temporary registers
    register int32_t *c0;
    register int32_t *c1;
    register int32_t *c2;
    register int32_t *c3;
    register int32_t a;
    register int32_t b0;
    register int32_t b1;
    register int32_t b2;
    register int32_t b3;
    __asm__ volatile(
        // Outer loop: Calculate four elements of C. Execute this loop P times
        "1: \n\t"
        "li %[c0],0 \n\t"
        "li %[c1],0 \n\t"
        "li %[c2],0 \n\t"
        "li %[c3],0 \n\t"
        "mv %[idx_b],%[start_b] \n\t"
        // Inner loop: Take one element of A to multiply with four elements of
        // B. Traverse A row major and B column major with four columns in
        // parallel. Do this loop N times per element
        "2: \n\t"
        "lw %[a], 0(%[idx_a]) \n\t"
        "lw %[b0], 0(%[idx_b]) \n\t"
        "lw %[b1], 4(%[idx_b]) \n\t"
        "lw %[b2], 8(%[idx_b]) \n\t"
        "lw %[b3],12(%[idx_b]) \n\t"
        // Traverse A row wise --> Increment A by one word
        "addi %[idx_a],%[idx_a],%[inc_a] \n\t"
        // Traverse B column wise --> Increment B by P words
        "addi %[idx_b],%[idx_b],%[inc_b] \n\t"
        "mul %[b0],%[a],%[b0] \n\t"
        "mul %[b1],%[a],%[b1] \n\t"
        "mul %[b2],%[a],%[b2] \n\t"
        "mul %[b3],%[a],%[b3] \n\t"
        "add %[c0],%[c0],%[b0] \n\t"
        "add %[c1],%[c1],%[b1] \n\t"
        "add %[c2],%[c2],%[b2] \n\t"
        "add %[c3],%[c3],%[b3] \n\t"
        "bne %[idx_a],%[end_a], 2b \n\t"
        // End of inner loop. Store the finished entries of C
        "sw %[c0], 0(%[idx_c]) \n\t"
        "sw %[c1], 4(%[idx_c]) \n\t"
        "sw %[c2], 8(%[idx_c]) \n\t"
        "sw %[c3], 12(%[idx_c]) \n\t"
        // A traversed one complete row + one extra word due to the
        // structure of the loop. Undo these increments to reset
        // `idx_a` to the first word in the row
        "addi %[idx_a], %[idx_a], %[adv_a] \n\t"
        // Increment the index of B and C by four words
        "addi %[start_b], %[start_b], %[adv_b] \n\t"
        "addi %[idx_c], %[idx_c], %[adv_c] \n\t"
        "bne %[idx_c], %[end_c], 1b \n\t"
        : [c0] "=&r"(c0), [c1] "=&r"(c1), [c2] "=&r"(c2), [c3] "=&r"(c3),
          [a] "=&r"(a), [b0] "=&r"(b0), [b1] "=&r"(b1), [b2] "=&r"(b2),
          [b3] "=&r"(b3), [idx_b] "+&r"(idx_b), [idx_a] "+&r"(start_a),
          [start_b] "+&r"(start_b), [idx_c] "+&r"(start_c)
        : [inc_a] "I"(4), [inc_b] "I"(4 * P), [adv_a] "I"(-4 * N),
          [adv_b] "I"(4 * 4), [adv_c] "I"(4 * 4), [end_a] "r"(end_a),
          [end_c] "r"(end_c)
        : "memory");
  }
}

static inline void mat_mul_asm(int32_t const *__restrict__ A,
                               int32_t const *__restrict__ B,
                               int32_t *__restrict__ C, uint32_t M, uint32_t N,
                               uint32_t P) {
  mat_mul_asm_parallel(A, B, C, M, N, P, 0, 1);
}
