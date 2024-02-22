// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
//         Sergio Mazzola, ETH Zurich

#include "xpulp/builtins_v2.h"

/* This library implements the matrix multiplication for several data widths
 * in Zmultiple different ways. The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 *
 * Note that all the matrices dimensions must be multiples of 4; these
 * kernels do not have clean-up code and remaining elements would not be
 * considered, leading to wrong results
 */

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_2x2_parallel_i16_rv32im
 * data type  = 16-bit integer
 * multi-core = yes
 * unrolling  = 4 elements of C per iteration (2x2 chunks)
 * simd       = no
 */
void matmul_unrolled_2x2_parallel_i16_rv32im(int16_t const *__restrict__ A,
                                             int16_t const *__restrict__ B,
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
        int16_t val_a00 = A[(i + 0) * N + k + 0];
        int16_t val_a01 = A[(i + 0) * N + k + 1];
        int16_t val_a10 = A[(i + 1) * N + k + 0];
        int16_t val_a11 = A[(i + 1) * N + k + 1];
        int16_t val_b00 = B[(k + 0) * P + j + 0];
        int16_t val_b01 = B[(k + 0) * P + j + 1];
        int16_t val_b10 = B[(k + 1) * P + j + 0];
        int16_t val_b11 = B[(k + 1) * P + j + 1];
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

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_4x2_parallel_i16_xpulpv2
 * data type  = 16-bit integer
 * multi-core = yes
 * unrolling  = 8 elements of C per iteration (4x2 chunks)
 * simd       = yes, Xpulpv2 intrinsics
 *
 * Original plp_mat_mult_i16p_xpulpv2 from pulp-dsp
 */
#ifdef __XPULPIMG
void matmul_unrolled_4x2_parallel_i16_xpulpv2(const int16_t *__restrict__ pSrcA,
                                              const int16_t *__restrict__ pSrcB,
                                              int32_t *__restrict__ pDstC,
                                              uint32_t M, uint32_t N,
                                              uint32_t P, uint32_t core_id,
                                              uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  for (k = core_id; k < P / 2; k += numThreads) {
    for (i = 0; i < M / 4; i++) {

      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum20 = 0;
      int32_t sum21 = 0;
      int32_t sum30 = 0;
      int32_t sum31 = 0;

      for (j = 0; j < N / 2; j++) {

        v2s aVec0 = *((v2s *)&(pSrcA[(i * 4) * N + (j * 2)]));
        v2s aVec1 = *((v2s *)&(pSrcA[(i * 4 + 1) * N + (j * 2)]));
        v2s aVec2 = *((v2s *)&(pSrcA[(i * 4 + 2) * N + (j * 2)]));
        v2s aVec3 = *((v2s *)&(pSrcA[(i * 4 + 3) * N + (j * 2)]));

        v2s bTemp0 = *((v2s *)&(pSrcB[(j * 2) * P + (k * 2)]));
        v2s bTemp1 = *((v2s *)&(pSrcB[(j * 2 + 1) * P + (k * 2)]));

        v2s bVec0 = __builtin_shuffle(bTemp0, bTemp1, (v2s){0, 2});
        v2s bVec1 = __builtin_shuffle(bTemp0, bTemp1, (v2s){1, 3});

        sum00 = __SUMDOTP2(aVec0, bVec0, sum00);
        sum01 = __SUMDOTP2(aVec0, bVec1, sum01);
        sum10 = __SUMDOTP2(aVec1, bVec0, sum10);
        sum11 = __SUMDOTP2(aVec1, bVec1, sum11);
        sum20 = __SUMDOTP2(aVec2, bVec0, sum20);
        sum21 = __SUMDOTP2(aVec2, bVec1, sum21);
        sum30 = __SUMDOTP2(aVec3, bVec0, sum30);
        sum31 = __SUMDOTP2(aVec3, bVec1, sum31);
      }

      pDstC[(i * 4) * P + (k * 2)] = sum00;
      pDstC[(i * 4) * P + (k * 2 + 1)] = sum01;
      pDstC[(i * 4 + 1) * P + (k * 2)] = sum10;
      pDstC[(i * 4 + 1) * P + (k * 2 + 1)] = sum11;
      pDstC[(i * 4 + 2) * P + (k * 2)] = sum20;
      pDstC[(i * 4 + 2) * P + (k * 2 + 1)] = sum21;
      pDstC[(i * 4 + 3) * P + (k * 2)] = sum30;
      pDstC[(i * 4 + 3) * P + (k * 2 + 1)] = sum31;
    }
  }
}
#endif

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_4x2_pincr_asm_parallel_i16_xpulpv2
 * data type  = 16-bit integer
 * multi-core = yes
 * unrolling  = 8 elements of C per iteration (4x2 chunks)
 * simd       = yes, Xpulpv2 intrinsics
 * other      = using pointer incrementing insteady of array
 *              indexing and loads/stores explicitly written
 *              in asm, for optimal register utilization
 *
 * Inspired from plp_mat_mult_i16p_xpulpv2 from pulp-dsp
 */
#ifdef __XPULPIMG
void matmul_unrolled_4x2_pincr_asm_parallel_i16_xpulpv2(
    const int16_t *__restrict__ pSrcA, const int16_t *__restrict__ pSrcB,
    int32_t *__restrict__ pDstC, uint32_t M, uint32_t N, uint32_t P,
    uint32_t core_id, uint32_t numThreads) {
  // Loop counter for P
  uint32_t k = 0;
  // Increment for A matrix = 1 row forward
  uint32_t const A_incr = N * sizeof(int16_t);
  // Decrement for A matrix = 3 rows backward and 2 words forward
  int32_t const A_decr =
      -(int)(N * 3 * sizeof(int16_t)) + 2 * (int)sizeof(int16_t);
  // Increment for B matrix = 1 row forward
  uint32_t const B_incr = P * sizeof(int16_t); // bytes in 1 row
  // Increment for C matrix = 1 row forward and 1 word backward
  uint32_t const C_incr = (P * sizeof(int32_t)) - sizeof(int32_t);

  for (k = core_id; k < P / 2; k += numThreads) {
    const int16_t *idx_a = &pSrcA[0];     // start_a
    int32_t *idx_c = &pDstC[k * 2];       // start_c
    int32_t const *end_c = &pDstC[P * M]; // actually (P * M) + (k * 2)

    while (idx_c < end_c) {

      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum20 = 0;
      int32_t sum21 = 0;
      int32_t sum30 = 0;
      int32_t sum31 = 0;

      int16_t const *end_a = idx_a + N;
      const int16_t *idx_b = &pSrcB[k * 2]; // start_b

      while (idx_a < end_a) {

        v2s aVec0, aVec1, aVec2, aVec3;
        v2s bTemp0, bTemp1;

        __asm__ volatile(
            "p.lw %[a0], %[a_incr](%[addr_a]!) \n\t"
            "p.lw %[a1], %[a_incr](%[addr_a]!) \n\t"
            "p.lw %[a2], %[a_incr](%[addr_a]!) \n\t"
            "p.lw %[a3], %[a_decr](%[addr_a]!) \n\t"
            "p.lw %[t0], %[b_incr](%[addr_b]!) \n\t"
            "p.lw %[t1], %[b_incr](%[addr_b]!) \n\t"
            : [a0] "=&r"(aVec0), [a1] "=&r"(aVec1), [a2] "=&r"(aVec2),
              [a3] "=&r"(aVec3), [t0] "=&r"(bTemp0), [t1] "=&r"(bTemp1),
              [addr_a] "+&r"(idx_a), [addr_b] "+&r"(idx_b)
            : [a_incr] "r"(A_incr), [a_decr] "r"(A_decr), [b_incr] "r"(B_incr)
            : "memory");
        /* The asm code above implements the following commented C code */
        // v2s aVec0 = *((v2s *)&(pSrcA[(i * 4) * N + (j * 2)]));
        // v2s aVec1 = *((v2s *)&(pSrcA[(i * 4 + 1) * N + (j * 2)]));
        // v2s aVec2 = *((v2s *)&(pSrcA[(i * 4 + 2) * N + (j * 2)]));
        // v2s aVec3 = *((v2s *)&(pSrcA[(i * 4 + 3) * N + (j * 2)]));
        // v2s bTemp0 = *((v2s *)&(pSrcB[(j * 2) * P + (k * 2)]));
        // v2s bTemp1 = *((v2s *)&(pSrcB[(j * 2 + 1) * P + (k * 2)]));

        v2s bVec0 = __builtin_shuffle(bTemp0, bTemp1, (v2s){0, 2});
        v2s bVec1 = __builtin_shuffle(bTemp0, bTemp1, (v2s){1, 3});

        sum00 = __SUMDOTP2(aVec0, bVec0, sum00);
        sum01 = __SUMDOTP2(aVec0, bVec1, sum01);
        sum10 = __SUMDOTP2(aVec1, bVec0, sum10);
        sum11 = __SUMDOTP2(aVec1, bVec1, sum11);
        sum20 = __SUMDOTP2(aVec2, bVec0, sum20);
        sum21 = __SUMDOTP2(aVec2, bVec1, sum21);
        sum30 = __SUMDOTP2(aVec3, bVec0, sum30);
        sum31 = __SUMDOTP2(aVec3, bVec1, sum31);
      }

      __asm__ volatile(
          "p.sw %[s00], 4(%[addr_c]!) \n\t"
          "p.sw %[s01], %[c_incr](%[addr_c]!) \n\t"
          "p.sw %[s10], 4(%[addr_c]!) \n\t"
          "p.sw %[s11], %[c_incr](%[addr_c]!) \n\t"
          "p.sw %[s20], 4(%[addr_c]!) \n\t"
          "p.sw %[s21], %[c_incr](%[addr_c]!) \n\t"
          "p.sw %[s30], 4(%[addr_c]!) \n\t"
          "p.sw %[s31], %[c_incr](%[addr_c]!) \n\t"
          : [addr_c] "+&r"(idx_c)
          : [s00] "r"(sum00), [s01] "r"(sum01), [s10] "r"(sum10),
            [s11] "r"(sum11), [s20] "r"(sum20), [s21] "r"(sum21),
            [s30] "r"(sum30), [s31] "r"(sum31), [c_incr] "r"(C_incr)
          : "memory");
      /* The asm code above implements the following commented C code */
      // pDstC[(i * 4) * P + (k * 2)] = sum00;
      // pDstC[(i * 4) * P + (k * 2 + 1)] = sum01;
      // pDstC[(i * 4 + 1) * P + (k * 2)] = sum10;
      // pDstC[(i * 4 + 1) * P + (k * 2 + 1)] = sum11;
      // pDstC[(i * 4 + 2) * P + (k * 2)] = sum20;
      // pDstC[(i * 4 + 2) * P + (k * 2 + 1)] = sum21;
      // pDstC[(i * 4 + 3) * P + (k * 2)] = sum30;
      // pDstC[(i * 4 + 3) * P + (k * 2 + 1)] = sum31;

      idx_a += N * 3;
    }
  }
}
#endif
