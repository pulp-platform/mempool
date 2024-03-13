// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich
//         Sergio Mazzola, ETH Zurich

#include "builtins_v2.h"

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
 * kernel     = matmul_unrolled_2x2_parallel_i8_rv32im
 * data type  = 8-bit integer
 * multi-core = yes
 * unrolling  = 4 elements of C per iteration (2x2 chunks)
 * simd       = no
 */
void matmul_unrolled_2x2_parallel_i8_rv32im(int8_t const *__restrict__ A,
                                            int8_t const *__restrict__ B,
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
        int8_t val_a00 = A[(i + 0) * N + k + 0];
        int8_t val_a01 = A[(i + 0) * N + k + 1];
        int8_t val_a10 = A[(i + 1) * N + k + 0];
        int8_t val_a11 = A[(i + 1) * N + k + 1];
        int8_t val_b00 = B[(k + 0) * P + j + 0];
        int8_t val_b01 = B[(k + 0) * P + j + 1];
        int8_t val_b10 = B[(k + 1) * P + j + 0];
        int8_t val_b11 = B[(k + 1) * P + j + 1];
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
 * kernel     = matmul_unrolled_2x4_parallel_i8_xpulpv2
 * data type  = 8-bit integer
 * multi-core = yes
 * unrolling  = 8 elements of C per iteration (2x4 chunks)
 * simd       = yes, Xpulpv2 intrinsics
 *
 * Original plp_mat_mult_i8p_xpulpv2 from pulp-dsp
 */
#ifdef __XPULPIMG
void matmul_unrolled_2x4_parallel_i8_xpulpv2(const int8_t *__restrict__ pSrcA,
                                             const int8_t *__restrict__ pSrcB,
                                             int32_t *__restrict__ pDstC,
                                             uint32_t M, uint32_t N, uint32_t P,
                                             uint32_t core_id,
                                             uint32_t numThreads) {
  static v4s mask0 = {0, 1, 4, 5};
  static v4s mask1 = {2, 3, 6, 7};
  static v4s mask2 = {0, 2, 4, 6};
  static v4s mask3 = {1, 3, 5, 7};

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  for (k = core_id; k < P / 4; k += numThreads) {
    for (i = 0; i < M / 2; i++) {

      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum02 = 0;
      int32_t sum03 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum12 = 0;
      int32_t sum13 = 0;

      for (j = 0; j < N / 4; j++) {

        v4s aVec0 = *((v4s *)&(pSrcA[(i * 2) * N + (j * 4)]));
        v4s aVec1 = *((v4s *)&(pSrcA[(i * 2 + 1) * N + (j * 4)]));

        v4s temp0 = *((v4s *)&(pSrcB[(j * 4) * P + (k * 4)]));
        v4s temp1 = *((v4s *)&(pSrcB[(j * 4 + 1) * P + (k * 4)]));
        v4s temp2 = *((v4s *)&(pSrcB[(j * 4 + 2) * P + (k * 4)]));
        v4s temp3 = *((v4s *)&(pSrcB[(j * 4 + 3) * P + (k * 4)]));

        v4s temp4 = __builtin_shuffle(temp0, temp1, mask0); // 0,1,4,5
        v4s temp5 = __builtin_shuffle(temp2, temp3, mask0); // 8,9,12,13
        v4s temp6 = __builtin_shuffle(temp0, temp1, mask1); // 2,3,6,7
        v4s temp7 = __builtin_shuffle(temp2, temp3, mask1); // 3,7,11,15

        v4s bVec0 = __builtin_shuffle(temp4, temp5, mask2); // 0,4,8,12
        v4s bVec1 = __builtin_shuffle(temp4, temp5, mask3); // 1,5,9,13
        v4s bVec2 = __builtin_shuffle(temp6, temp7, mask2); // 2,6,10,14
        v4s bVec3 = __builtin_shuffle(temp6, temp7, mask3); // 3,7,11,15

        sum00 = __SUMDOTP4(aVec0, bVec0, sum00);
        sum01 = __SUMDOTP4(aVec0, bVec1, sum01);
        sum02 = __SUMDOTP4(aVec0, bVec2, sum02);
        sum03 = __SUMDOTP4(aVec0, bVec3, sum03);
        sum10 = __SUMDOTP4(aVec1, bVec0, sum10);
        sum11 = __SUMDOTP4(aVec1, bVec1, sum11);
        sum12 = __SUMDOTP4(aVec1, bVec2, sum12);
        sum13 = __SUMDOTP4(aVec1, bVec3, sum13);
      }

      pDstC[(i * 2) * P + (k * 4)] = sum00;
      pDstC[(i * 2) * P + (k * 4 + 1)] = sum01;
      pDstC[(i * 2) * P + (k * 4 + 2)] = sum02;
      pDstC[(i * 2) * P + (k * 4 + 3)] = sum03;
      pDstC[(i * 2 + 1) * P + (k * 4)] = sum10;
      pDstC[(i * 2 + 1) * P + (k * 4 + 1)] = sum11;
      pDstC[(i * 2 + 1) * P + (k * 4 + 2)] = sum12;
      pDstC[(i * 2 + 1) * P + (k * 4 + 3)] = sum13;
    }
  }
}
#endif

/*
 * Matrix multiplication ----------------------------------
 * kernel     = matmul_unrolled_2x4_pincr_asm_parallel_i8_xpulpv2
 * data type  = 8-bit integer
 * multi-core = yes
 * unrolling  = 8 elements of C per iteration (2x4 chunks)
 * simd       = yes, Xpulpv2 intrinsics
 * other      = using pointer incrementing insteady of array
 *              indexing and loads/stores explicitly written
 *              in asm, for optimal register utilization
 *
 * Inspired from plp_mat_mult_i8p_xpulpv2 from pulp-dsp
 */
#ifdef __XPULPIMG
void matmul_unrolled_2x4_pincr_asm_parallel_i8_xpulpv2(
    const int8_t *__restrict__ pSrcA, const int8_t *__restrict__ pSrcB,
    int32_t *__restrict__ pDstC, uint32_t M, uint32_t N, uint32_t P,
    uint32_t core_id, uint32_t numThreads) {
  // Masks for shuffles
  static v4s mask0 = {0, 1, 4, 5};
  static v4s mask1 = {2, 3, 6, 7};
  static v4s mask2 = {0, 2, 4, 6};
  static v4s mask3 = {1, 3, 5, 7};

  // Loop counter for P
  uint32_t k = 0;
  // Row decrement for A matrix
  int32_t const N_decr = -(int)N + 4;
  // Row increment for C matrix
  uint32_t const P_incr = (P * 4) - 12;

  for (k = core_id; k < P / 4; k += numThreads) {
    const int8_t *idx_a = &pSrcA[0];      // start_a
    int32_t *idx_c = &pDstC[k * 4];       // start_c
    int32_t const *end_c = &pDstC[P * M]; // actually (P * M) + (k * 4)
    while (idx_c < end_c) {

      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum02 = 0;
      int32_t sum03 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum12 = 0;
      int32_t sum13 = 0;

      int8_t const *end_a = idx_a + N;
      const int8_t *idx_b = &pSrcB[k * 4]; // start_b
      while (idx_a < end_a) {

        v4s aVec0, aVec1;
        v4s temp0, temp1, temp2, temp3;

        __asm__ volatile(
            "p.lw %[a0], %[a_incr](%[addr_a]!) \n\t"
            "p.lw %[a1], %[a_decr](%[addr_a]!) \n\t"
            "p.lw %[t0], %[b_incr](%[addr_b]!) \n\t"
            "p.lw %[t1], %[b_incr](%[addr_b]!) \n\t"
            "p.lw %[t2], %[b_incr](%[addr_b]!) \n\t"
            "p.lw %[t3], %[b_incr](%[addr_b]!) \n\t"
            : [a0] "=&r"(aVec0), [a1] "=&r"(aVec1), [t0] "=&r"(temp0),
              [t1] "=&r"(temp1), [t2] "=&r"(temp2), [t3] "=&r"(temp3),
              [addr_a] "+&r"(idx_a), [addr_b] "+&r"(idx_b)
            : [a_incr] "r"(N), [a_decr] "r"(N_decr), [b_incr] "r"(P)
            : "memory");
        /* The asm code above implements the following commented C code */
        // go to next row, same column
        // v4s aVec0 = *((v4s *)idx_a); idx_a += N;
        // go to previous row, one column forward
        // v4s aVec1 = *((v4s *)idx_a); idx_a -= N - 4;
        // v4s temp0 = *((v4s *)idx_b); idx_b += P;
        // v4s temp1 = *((v4s *)idx_b); idx_b += P;
        // v4s temp2 = *((v4s *)idx_b); idx_b += P;
        // v4s temp3 = *((v4s *)idx_b); idx_b += P;

        // Shuffles to transpose at runtime the chunk extracted from B before
        // multiplying with A chunk temp0-3 variables needed because shuffles
        // use rD as source, but also modify it, thus we need a copy of their
        // content to use it twice in their original form
        v4s temp4 = __builtin_shuffle(temp0, temp1, mask0); // 0,1,4,5
        v4s temp5 = __builtin_shuffle(temp2, temp3, mask0); // 8,9,12,13
        v4s temp6 = __builtin_shuffle(temp0, temp1, mask1); // 2,3,6,7
        v4s temp7 = __builtin_shuffle(temp2, temp3, mask1); // 3,7,11,15

        v4s bVec0 = __builtin_shuffle(temp4, temp5, mask2); // 0,4,8,12
        v4s bVec1 = __builtin_shuffle(temp4, temp5, mask3); // 1,5,9,13
        v4s bVec2 = __builtin_shuffle(temp6, temp7, mask2); // 2,6,10,14
        v4s bVec3 = __builtin_shuffle(temp6, temp7, mask3); // 3,7,11,15

        sum00 = __SUMDOTP4(aVec0, bVec0, sum00);
        sum01 = __SUMDOTP4(aVec0, bVec1, sum01);
        sum02 = __SUMDOTP4(aVec0, bVec2, sum02);
        sum03 = __SUMDOTP4(aVec0, bVec3, sum03);
        sum10 = __SUMDOTP4(aVec1, bVec0, sum10);
        sum11 = __SUMDOTP4(aVec1, bVec1, sum11);
        sum12 = __SUMDOTP4(aVec1, bVec2, sum12);
        sum13 = __SUMDOTP4(aVec1, bVec3, sum13);
      }

      __asm__ volatile(
          "p.sw %[s00], 4(%[addr_c]!) \n\t"
          "p.sw %[s01], 4(%[addr_c]!) \n\t"
          "p.sw %[s02], 4(%[addr_c]!) \n\t"
          "p.sw %[s03], %[c_incr](%[addr_c]!) \n\t"
          "p.sw %[s10], 4(%[addr_c]!) \n\t"
          "p.sw %[s11], 4(%[addr_c]!) \n\t"
          "p.sw %[s12], 4(%[addr_c]!) \n\t"
          "p.sw %[s13], %[c_incr](%[addr_c]!) \n\t"
          : [addr_c] "+&r"(idx_c)
          : [s00] "r"(sum00), [s01] "r"(sum01), [s02] "r"(sum02),
            [s03] "r"(sum03), [s10] "r"(sum10), [s11] "r"(sum11),
            [s12] "r"(sum12), [s13] "r"(sum13), [c_incr] "r"(P_incr)
          : "memory");
      /* The asm code above implements the following commented C code */
      // *(idx_c++) = sum00;
      // *(idx_c++) = sum01;
      // *(idx_c++) = sum02;
      // *(idx_c) = sum03; idx_c += P - 3;
      // *(idx_c++) = sum10;
      // *(idx_c++) = sum11;
      // *(idx_c++) = sum12;
      // *(idx_c) = sum13; idx_c += P - 3;

      idx_a += N; // adjust A matrix pointer
    }
  }
}
#endif
