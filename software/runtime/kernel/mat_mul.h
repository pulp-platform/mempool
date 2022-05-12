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
  uint32_t chunks = (M * P) / numThreads;
  uint32_t chunks_left = (M * P) - (chunks * numThreads);
  uint32_t start;
  if (chunks_left < id) {
    start = id * chunks + chunks_left;
  } else {
    chunks++;
    start = id * chunks;
  }
  uint32_t end = start + chunks;
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

void mat_mul_unrolled_2x2_parallel(int32_t const *__restrict__ A,
                                   int32_t const *__restrict__ B,
                                   int32_t *__restrict__ C, uint32_t M,
                                   uint32_t N, uint32_t P, uint32_t id,
                                   uint32_t numThreads) {
  // Parallelize by assigning each core one row
  uint32_t const c = 8; // How many columns to split the matrix into
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);
  for (uint32_t i = 2 * (id / c); i < M; i += 2 * (numThreads / c)) {
    for (uint32_t j = c_start; j < c_end; j += 2) {
      int32_t c00 = 0;
      int32_t c01 = 0;
      int32_t c10 = 0;
      int32_t c11 = 0;
      for (uint32_t k = 0; k < N; k += 2) {
        // Explicitly load the values first to help with scheduling
        int32_t val_a00 = A[(i + 0) * N + k + 0];
        int32_t val_a01 = A[(i + 0) * N + k + 1];
        int32_t val_a10 = A[(i + 1) * N + k + 0];
        int32_t val_a11 = A[(i + 1) * N + k + 1];
        int32_t val_b00 = B[(k + 0) * P + j + 0];
        int32_t val_b01 = B[(k + 0) * P + j + 1];
        int32_t val_b10 = B[(k + 1) * P + j + 0];
        int32_t val_b11 = B[(k + 1) * P + j + 1];
        c00 += val_a00 * val_b00;
        c00 += val_a01 * val_b10;
        c01 += val_a00 * val_b01;
        c01 += val_a01 * val_b11;
        c10 += val_a10 * val_b00;
        c10 += val_a11 * val_b10;
        c11 += val_a10 * val_b01;
        c11 += val_a11 * val_b11;
      }
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
    }
  }
}

void mat_mul_unrolled_4x4_parallel(int32_t const *__restrict__ A,
                                   int32_t const *__restrict__ B,
                                   int32_t *__restrict__ C, uint32_t M,
                                   uint32_t N, uint32_t P, uint32_t id,
                                   uint32_t numThreads) {
  // Parallelize by assigning each core one row
  uint32_t const c = 16; // How many columns to split the matrix into
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);
  for (uint32_t i = 4 * (id / c); i < M; i += 4 * (numThreads / c)) {
    for (uint32_t j = c_start; j < c_end; j += 4) {
      // Initialize 4x4 output tile
      int32_t c00 = 0, c01 = 0, c02 = 0, c03 = 0;
      int32_t c10 = 0, c11 = 0, c12 = 0, c13 = 0;
      int32_t c20 = 0, c21 = 0, c22 = 0, c23 = 0;
      int32_t c30 = 0, c31 = 0, c32 = 0, c33 = 0;
      for (uint32_t k = 0; k < N; k += 1) {
        // Explicitly load the values first to help with scheduling
        int32_t b0 = B[k * P + j + 0];
        int32_t b1 = B[k * P + j + 1];
        int32_t b2 = B[k * P + j + 2];
        int32_t b3 = B[k * P + j + 3];
        // A could be local with scrambling
        int32_t a0 = A[(i + 0) * N + k];
        int32_t a1 = A[(i + 1) * N + k];
        int32_t a2 = A[(i + 2) * N + k];
        int32_t a3 = A[(i + 3) * N + k];
        // Compute
        c00 += a0 * b0;
        c01 += a0 * b1;
        c02 += a0 * b2;
        c03 += a0 * b3;
        c10 += a1 * b0;
        c11 += a1 * b1;
        c12 += a1 * b2;
        c13 += a1 * b3;
        c20 += a2 * b0;
        c21 += a2 * b1;
        c22 += a2 * b2;
        c23 += a2 * b3;
        c30 += a3 * b0;
        c31 += a3 * b1;
        c32 += a3 * b2;
        c33 += a3 * b3;
      }
      // Store
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 0) * P + j + 2] = c02;
      C[(i + 0) * P + j + 3] = c03;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
      C[(i + 1) * P + j + 2] = c12;
      C[(i + 1) * P + j + 3] = c13;
      C[(i + 2) * P + j + 0] = c20;
      C[(i + 2) * P + j + 1] = c21;
      C[(i + 2) * P + j + 2] = c22;
      C[(i + 2) * P + j + 3] = c23;
      C[(i + 3) * P + j + 0] = c30;
      C[(i + 3) * P + j + 1] = c31;
      C[(i + 3) * P + j + 2] = c32;
      C[(i + 3) * P + j + 3] = c33;
    }
  }
}

#define NN (256)

void mat_mul_unrolled_4x4_parallel_asm(int32_t const *__restrict__ A,
                                       int32_t const *__restrict__ B,
                                       int32_t *__restrict__ C, uint32_t M,
                                       uint32_t N, uint32_t P, uint32_t id,
                                       uint32_t numThreads) {
  // Parallelize by assigning each tile one row
  uint32_t const c = 16; // How many columns to split the matrix into
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);
  for (uint32_t i = 4 * (id / c); i < M; i += 4 * (numThreads / c)) {
    for (uint32_t j = c_start; j < c_end; j += 4) {

      // Address registers
      int32_t const *addr_a = &A[i * N];
      int32_t const *addr_b = &B[j];
      int32_t const *end_b = &B[N * P + j];
      int32_t const *addr_c = &C[i * P + j];
      int32_t const N3_1 = (-3 * (int32_t)N + 1) * 4;
      int32_t const P_3 = ((int32_t)P - 3) * 4;

      register int32_t k asm("x1") = (int32_t)end_b;

      //      x12 x13 x14 x15
      //
      // x3   x16 x17 x18 x19
      // x4   x20 x21 x22 x23
      // x10  x24 x25 x26 x27
      // x11  x28 x29 x30 x31
      //
      //
      __asm__ volatile(
          ".balign 16 \n\t"
          // Outer loop: Initialize and preload. Execute this loop P times
          // TODO arrange
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.lw x15, %[P_3](%[addr_b]!) \n\t" // Increment by P-3
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t" // Increment by -3N+1
          // Initial computation + prefetching
          "mul x16,  x3, x12 \n\t"
          "mul x17,  x3, x13 \n\t"
          "mul x18,  x3, x14 \n\t"
          "mul x19,  x3, x15 \n\t"
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "mul x20,  x4, x12 \n\t"
          "mul x21,  x4, x13 \n\t"
          "mul x22,  x4, x14 \n\t"
          "mul x23,  x4, x15 \n\t"
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "mul x24, x10, x12 \n\t"
          "mul x25, x10, x13 \n\t"
          "mul x26, x10, x14 \n\t"
          "mul x27, x10, x15 \n\t"
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "mul x28, x11, x12 \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "mul x29, x11, x13 \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "mul x30, x11, x14 \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "mul x31, x11, x15 \n\t"
          "p.lw x15, %[P_3](%[addr_b]!) \n\t"  // Increment by P-3
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t" // Increment by -3N+1
          // Inner loop: Do this loop N times
          "1: \n\t"
          "p.mac x16,  x3, x12 \n\t"
          "p.mac x17,  x3, x13 \n\t"
          "p.mac x20,  x4, x12 \n\t"
          "p.mac x21,  x4, x13 \n\t"
          "p.mac x18,  x3, x14 \n\t"
          "p.mac x22,  x4, x14 \n\t"
          "p.mac x19,  x3, x15 \n\t"
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "p.mac x23,  x4, x15 \n\t"
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "p.mac x24, x10, x12 \n\t"
          "p.mac x28, x11, x12 \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "p.mac x25, x10, x13 \n\t"
          "p.mac x29, x11, x13 \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "p.mac x26, x10, x14 \n\t"
          "p.mac x30, x11, x14 \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.mac x27, x10, x15 \n\t"
          "p.mac x31, x11, x15 \n\t"
          "p.lw x15, %[P_3](%[addr_b]!) \n\t" // Increment by P-3
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t" // Increment by -3N+1
          "bne %[addr_b], x1, 1b \n\t"
          // Loop done store
          "p.mac x16,  x3, x12 \n\t"
          "p.mac x17,  x3, x13 \n\t"
          "p.mac x18,  x3, x14 \n\t"
          "p.sw x16, 4(%[addr_c]!) \n\t"
          "p.mac x19,  x3, x15 \n\t"
          "p.sw x17, 4(%[addr_c]!) \n\t"
          "p.mac x20,  x4, x12 \n\t"
          "p.sw x18, 4(%[addr_c]!) \n\t"
          "p.mac x21,  x4, x13 \n\t"
          "p.sw x19, %[P_3](%[addr_c]!) \n\t"
          "p.mac x22,  x4, x14 \n\t"
          "p.sw x20, 4(%[addr_c]!) \n\t"
          "p.mac x23,  x4, x15 \n\t"
          "p.sw x21, 4(%[addr_c]!) \n\t"
          "p.mac x24, x10, x12 \n\t"
          "p.sw x22, 4(%[addr_c]!) \n\t"
          "p.mac x25, x10, x13 \n\t"
          "p.sw x23, %[P_3](%[addr_c]!) \n\t"
          "p.mac x26, x10, x14 \n\t"
          "p.sw x24, 4(%[addr_c]!) \n\t"
          "p.mac x27, x10, x15 \n\t"
          "p.sw x25, 4(%[addr_c]!) \n\t"
          "p.mac x28, x11, x12 \n\t"
          "p.sw x26, 4(%[addr_c]!) \n\t"
          "p.mac x29, x11, x13 \n\t"
          "p.sw x27, %[P_3](%[addr_c]!) \n\t"
          "p.mac x30, x11, x14 \n\t"
          "p.sw x28, 4(%[addr_c]!) \n\t"
          "p.mac x31, x11, x15 \n\t"
          "p.sw x29, 4(%[addr_c]!) \n\t"
          "p.sw x30, 4(%[addr_c]!) \n\t"
          "p.sw x31, %[P_3](%[addr_c]!) \n\t"
          : [addr_a] "+&r"(addr_a), [addr_b] "+&r"(addr_b),
            [addr_c] "+&r"(addr_c) // Outputs
          : [N3_1] "r"(N3_1), [P_3] "r"(P_3), [x1] "r"(k),
            [N] "I"(NN * 4) // Inputs
          : "x3", "x4", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17",
            "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",
            "x27", "x28", "x29", "x30", "x31", "memory"); // Clobber
    }
  }
}

void mat_mul_unrolled2_shifted_parallel(int32_t const *__restrict__ A,
                                        int32_t const *__restrict__ B,
                                        int32_t *__restrict__ C, uint32_t M,
                                        uint32_t N, uint32_t P, uint32_t id,
                                        uint32_t numThreads) {
  // Parallelize by assigning each core one quarter of a row
  for (uint32_t i = 2 * id; i < M; i += 2 * numThreads) {
    for (uint32_t j = 0; j < P; j += 2) {
      int32_t c00 = 0;
      int32_t c01 = 0;
      int32_t c10 = 0;
      int32_t c11 = 0;
      for (uint32_t k = 0; k < N; k += 2) {
        // Explicitly load the values first to help with scheduling
        int32_t val_a00 = A[(i + 0) * N + k + 0];
        int32_t val_a01 = A[(i + 0) * N + k + 1];
        int32_t val_a10 = A[(i + 1) * N + k + 0];
        int32_t val_a11 = A[(i + 1) * N + k + 1];
        int32_t val_b00 = B[(k + 0) * P + j + 0];
        int32_t val_b01 = B[(k + 0) * P + j + 1];
        int32_t val_b10 = B[(k + 1) * P + j + 0];
        int32_t val_b11 = B[(k + 1) * P + j + 1];
        c00 += val_a00 * val_b00;
        c00 += val_a01 * val_b10;
        c01 += val_a00 * val_b01;
        c01 += val_a01 * val_b11;
        c10 += val_a10 * val_b00;
        c10 += val_a11 * val_b10;
        c11 += val_a10 * val_b01;
        c11 += val_a11 * val_b11;
      }
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
    }
  }
}

void mat_mul_unrolled_parallel_finegrained(int32_t const *__restrict__ A,
                                           int32_t const *__restrict__ B,
                                           int32_t *__restrict__ C, uint32_t M,
                                           uint32_t N, uint32_t P, uint32_t id,
                                           uint32_t numThreads) {
  // Merge outer loops to balance the workload
  // Chunks must be multiple of four
  uint32_t workload = (M * P) / 4;
  uint32_t chunks = workload / numThreads;
  uint32_t chunks_left = workload - (numThreads * chunks);
  uint32_t start;
  chunks *= 4;
  if (chunks_left < id) {
    start = id * chunks + chunks_left * 4;
  } else {
    chunks += 4;
    start = id * chunks;
  }
  uint32_t end = start + chunks;
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
  for (uint32_t i = id; i < M; i += numThreads) {
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
        ".balign 16 \n\t"
        "2: \n\t"
        "lw %[a], 0(%[idx_a]) \n\t"
        "lw %[b0], 0(%[idx_b]) \n\t"
        "lw %[b1], 4(%[idx_b]) \n\t"
        "lw %[b2], 8(%[idx_b]) \n\t"
        "lw %[b3],12(%[idx_b]) \n\t"
        // Traverse A row wise --> Increment A by one word
        "addi %[idx_a],%[idx_a],%[inc_a] \n\t"
        // Traverse B column wise --> Increment B by P words
        "add %[idx_b],%[idx_b],%[inc_b] \n\t"
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
        "add %[idx_a], %[idx_a], %[adv_a] \n\t"
        // Increment the index of B and C by four words
        "addi %[start_b], %[start_b], %[adv_b] \n\t"
        "addi %[idx_c], %[idx_c], %[adv_c] \n\t"
        "bne %[idx_c], %[end_c], 1b \n\t"
        : [c0] "=&r"(c0), [c1] "=&r"(c1), [c2] "=&r"(c2), [c3] "=&r"(c3),
          [a] "=&r"(a), [b0] "=&r"(b0), [b1] "=&r"(b1), [b2] "=&r"(b2),
          [b3] "=&r"(b3), [idx_b] "+&r"(idx_b), [idx_a] "+&r"(start_a),
          [start_b] "+&r"(start_b), [idx_c] "+&r"(start_c)
        : [inc_a] "I"(4), [inc_b] "r"(4 * P), [adv_a] "r"(-4 * (int)N),
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
