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

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_2x2_parallel_i32_rv32im
 * data type  = 32-bit integer
 * multi-core = yes
 * unrolling  = 4 elements of C per iteration (2x2 chunks)
 * simd       = no
 */
void matmul_unrolled_2x2_parallel_i32_rv32im(int32_t const *__restrict__ A,
                                             int32_t const *__restrict__ B,
                                             int32_t *__restrict__ C,
                                             uint32_t M, uint32_t N, uint32_t P,
                                             uint32_t id, uint32_t numThreads) {
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

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_2x2_parallel_i32_xpulpv2
 * data type  = 32-bit integer
 * multi-core = yes
 * unrolling  = 4 elements of C per iteration (2x2 chunks)
 * simd       = no
 * other      = loads/stores explicitly written in asm
 *              for optimal register utilization
 */
#ifdef __XPULPIMG
void matmul_unrolled_2x2_parallel_i32_xpulpv2(int32_t const *__restrict__ A,
                                              int32_t const *__restrict__ B,
                                              int32_t *__restrict__ C,
                                              uint32_t M, uint32_t N,
                                              uint32_t P, uint32_t id,
                                              uint32_t numThreads) {
  // Parallelize by assigning each core one row
  uint32_t const c = 8; // How many columns to split the matrix into
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);

  uint32_t const A_incr = (N * sizeof(int32_t)) - sizeof(int32_t);
  uint32_t const B_incr = (P * sizeof(int32_t)) - sizeof(int32_t);

  for (uint32_t i = 2 * (id / c); i < M; i += 2 * (numThreads / c)) {
    for (uint32_t j = c_start; j < c_end; j += 2) {
      int32_t c00 = 0;
      int32_t c01 = 0;
      int32_t c10 = 0;
      int32_t c11 = 0;

      for (uint32_t k = 0; k < N; k += 2) {
        const int32_t *idx_a = &A[i * N + k];
        const int32_t *idx_b = &B[k * P + j];
        int32_t val_a00, val_a01, val_a10, val_a11, val_b00, val_b01, val_b10,
            val_b11;
        __asm__ volatile(
            "p.lw %[a00], 4(%[addr_a]!) \n\t"
            "p.lw %[a01], %[a_incr](%[addr_a]!) \n\t"
            "p.lw %[a10], 4(%[addr_a]!) \n\t"
            "p.lw %[a11], 0(%[addr_a]) \n\t"
            "p.lw %[b00], 4(%[addr_b]!) \n\t"
            "p.lw %[b01], %[b_incr](%[addr_b]!) \n\t"
            "p.lw %[b10], 4(%[addr_b]!) \n\t"
            "p.lw %[b11], 0(%[addr_b]) \n\t"
            : [a00] "=&r"(val_a00), [a01] "=&r"(val_a01), [a10] "=&r"(val_a10),
              [a11] "=&r"(val_a11), [b00] "=&r"(val_b00), [b01] "=&r"(val_b01),
              [b10] "=&r"(val_b10), [b11] "=&r"(val_b11), [addr_a] "+&r"(idx_a),
              [addr_b] "+&r"(idx_b)
            : [a_incr] "r"(A_incr), [b_incr] "r"(B_incr)
            : "memory");
        /* The asm code above implements the following commented C code */
        // int32_t val_a00 = A[(i + 0) * N + k + 0];
        // int32_t val_a01 = A[(i + 0) * N + k + 1];
        // int32_t val_a10 = A[(i + 1) * N + k + 0];
        // int32_t val_a11 = A[(i + 1) * N + k + 1];
        // int32_t val_b00 = B[(k + 0) * P + j + 0];
        // int32_t val_b01 = B[(k + 0) * P + j + 1];
        // int32_t val_b10 = B[(k + 1) * P + j + 0];
        // int32_t val_b11 = B[(k + 1) * P + j + 1];
        c00 += val_a00 * val_b00;
        c00 += val_a01 * val_b10;
        c01 += val_a00 * val_b01;
        c01 += val_a01 * val_b11;
        c10 += val_a10 * val_b00;
        c10 += val_a11 * val_b10;
        c11 += val_a10 * val_b01;
        c11 += val_a11 * val_b11;
      }
      int32_t *idx_c = &C[i * P + j];
      __asm__ volatile("p.sw %[s00], 4(%[addr_c]!) \n\t"
                       "p.sw %[s01], %[c_incr](%[addr_c]!) \n\t"
                       "p.sw %[s10], 4(%[addr_c]!) \n\t"
                       "p.sw %[s11], 0(%[addr_c]) \n\t"
                       : [addr_c] "+&r"(idx_c)
                       : [s00] "r"(c00), [s01] "r"(c01), [s10] "r"(c10),
                         [s11] "r"(c11), [c_incr] "r"(B_incr)
                       : "memory");
      /* The asm code above implements the following commented C code */
      // C[(i + 0) * P + j + 0] = c00;
      // C[(i + 0) * P + j + 1] = c01;
      // C[(i + 1) * P + j + 0] = c10;
      // C[(i + 1) * P + j + 1] = c11;
    }
  }
}
#endif
