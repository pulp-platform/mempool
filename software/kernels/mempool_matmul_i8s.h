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
 * kernel     = matmul_unrolled_2x4_i8_xpulpv2
 * data type  = 8-bit integer
 * multi-core = no
 * unrolling  = 8 elements of C per iteration (2x4 chunks)
 * simd       = yes, Xpulpv2 intrinsics
 *
 * Original plp_mat_mult_i8s_xpulpv2 from pulp-dsp
 */
#ifdef __XPULPIMG
void matmul_unrolled_2x4_i8_xpulpv2(const int8_t *__restrict__ pSrcA,
                                    const int8_t *__restrict__ pSrcB,
                                    int32_t *__restrict__ pDstC, uint32_t M,
                                    uint32_t N, uint32_t P) {
  static v4s mask0 = {0, 1, 4, 5};
  static v4s mask1 = {2, 3, 6, 7};
  static v4s mask2 = {0, 2, 4, 6};
  static v4s mask3 = {1, 3, 5, 7};

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  for (i = 0; i < M / 2; i++) {
    for (k = 0; k < P / 4; k++) {

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
