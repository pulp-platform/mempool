// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library applies a softmax over an entire matrix.
 * A is the M x N input matrix, B stores the resulting matrix
 */

#pragma once
#include "builtins_v2.h"

void softmax_parallel_2x8_f8vec(const __fp8 *__restrict__ A,
                                __fp8 *__restrict__ B, uint32_t M, uint32_t N,
                                uint32_t core_id, uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  const unsigned ShuffleMask0 = 0x04040404; // [a b c d] => [d d d d]
  const unsigned ShuffleMask1 = 0x05050505; // [a b c d] => [c c c c]
  const unsigned ShuffleMask2 = 0x06060606; // [a b c d] => [b b b b]
  const unsigned ShuffleMask3 = 0x07070707; // [a b c d] => [a a a a]

  float Sixth = 0.167f;
  float Half = 0.5f;
  float One = 1.0f;
  float init = 0.5f;
  v4b vSixth, vHalf, vOne, max_init;

  asm volatile(
      "vfcpka.b.s %[vSixth], %[Sixth], %[Sixth];"
      "vfcpka.b.s %[vHalf], %[Half], %[Half];"
      "vfcpka.b.s %[vOne], %[One], %[One];"
      "vfcpka.b.s %[max_init], %[init], %[init];"
      "vfcpkb.b.s %[vSixth], %[Sixth], %[Sixth];"
      "vfcpkb.b.s %[vHalf], %[Half], %[Half];"
      "vfcpkb.b.s %[vOne], %[One], %[One];"
      "vfcpkb.b.s %[max_init], %[init], %[init];"
      : [vSixth] "+&r"(vSixth), [vHalf] "+&r"(vHalf), [vOne] "+&r"(vOne),
        [max_init] "+&r"(max_init)
      : [Sixth] "r"(Sixth), [Half] "r"(Half), [One] "r"(One), [init] "r"(init));

  for (i = core_id * 2; i < M; i += numThreads * 2) {

    // 1) Find the row-wise maximum value
    v4b max0 = max_init;
    v4b max1 = max_init;

    for (j = 0; j < N; j += 8) {

      v4b aVec00 = *(v4b *)&(A[i * N + j]);       // aVec00 = [a03 a02 a01 a00]
      v4b aVec01 = *(v4b *)&(A[i * N + j + 4]);   // aVec01 = [a07 a06 a05 a04]
      v4b aVec10 = *(v4b *)&(A[(i + 1) * N + j]); // aVec10 = [a13 a12 a11 a10]
      v4b aVec11 =
          *(v4b *)&(A[(i + 1) * N + j + 4]); // aVec11 = [a17 a16 a15 a14]

      v4b temp0, temp1;

      asm volatile(
          // Find max value (no full reduction)
          "vfmax.b %[temp0], %[aVec00], %[aVec01];"
          "vfmax.b %[temp1], %[aVec10], %[aVec11];"
          "vfmax.b %[max0], %[max0], %[temp0];"
          "vfmax.b %[max1], %[max1], %[temp1];"
          : [max0] "+&r"(max0), [max1] "+&r"(max1), [temp0] "+&r"(temp0),
            [temp1] "+&r"(temp1)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    // Potential max elements:
    v4b x0, x1, x2, x3;
    v4b pmax10, pmax11, pmax12, pmax13;

    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.b %[x0], %[max0], %[ShuffleMask0];"
        "pv.shuffle2.b %[x1], %[max0], %[ShuffleMask1];"
        "pv.shuffle2.b %[x2], %[max0], %[ShuffleMask2];"
        "pv.shuffle2.b %[x3], %[max0], %[ShuffleMask3];"
        "pv.shuffle2.b %[pmax10], %[max1], %[ShuffleMask0];"
        "pv.shuffle2.b %[pmax11], %[max1], %[ShuffleMask1];"
        "pv.shuffle2.b %[pmax12], %[max1], %[ShuffleMask2];"
        "pv.shuffle2.b %[pmax13], %[max1], %[ShuffleMask3];"
        "vfmax.b %[x0], %[x0], %[x1];"
        "vfmax.b %[x1], %[x2], %[x3];"
        "vfmax.b %[x2], %[pmax10], %[pmax11];"
        "vfmax.b %[x3], %[pmax12], %[pmax13];"
        "vfmax.b %[max0], %[x0], %[x1];"
        "vfmax.b %[max1], %[x2], %[x3];"
        : [max0] "+&r"(max0), [max1] "+&r"(max1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [x2] "+&r"(x2), [x3] "+&r"(x3),
          [pmax10] "+&r"(pmax10), [pmax11] "+&r"(pmax11),
          [pmax12] "+&r"(pmax12), [pmax13] "+&r"(pmax13)
        : [ShuffleMask0] "r"(ShuffleMask0), [ShuffleMask1] "r"(ShuffleMask1),
          [ShuffleMask2] "r"(ShuffleMask2), [ShuffleMask3] "r"(ShuffleMask3));

    // 2) Compute exp(x - max)
    // Store sum value in x0, x1
    x0 = (v4b)0.0f;
    x1 = (v4b)0.0f;

    for (j = 0; j < N; j += 8) {

      v4b aVec00 = *(v4b *)&(A[i * N + j]);       // aVec00 = [a03 a02 a01 a00]
      v4b aVec01 = *(v4b *)&(A[i * N + j + 4]);   // aVec01 = [a07 a06 a05 a04]
      v4b aVec10 = *(v4b *)&(A[(i + 1) * N + j]); // aVec10 = [a13 a12 a11 a10]
      v4b aVec11 =
          *(v4b *)&(A[(i + 1) * N + j + 4]); // aVec11 = [a17 a16 a15 a14]

      // Compute x' = x - max(x)
      asm volatile("vfsub.b %[aVec00], %[aVec00], %[max0];"
                   "vfsub.b %[aVec01], %[aVec01], %[max0];"
                   "vfsub.b %[aVec10], %[aVec10], %[max1];"
                   "vfsub.b %[aVec11], %[aVec11], %[max1];"
                   : [aVec00] "+&r"(aVec00), [aVec01] "+&r"(aVec01),
                     [aVec10] "+&r"(aVec10), [aVec11] "+&r"(aVec11)
                   : [max0] "r"(max0), [max1] "r"(max1));

      v4b xCu10, xCu11;
      v4b exp00, exp01, exp10, exp11;

      // Approximate exp with Taylor Series
      asm volatile(
          "vfmul.b %[xSq00], %[aVec00], %[aVec00];" // x^2
          "vfmul.b %[xSq01], %[aVec01], %[aVec01];"
          "vfmul.b %[xSq10], %[aVec10], %[aVec10];"
          "vfmul.b %[xSq11], %[aVec11], %[aVec11];"
          "vfmul.b %[xCu00], %[xSq00], %[aVec00];" // x^3
          "vfmul.b %[xCu01], %[xSq01], %[aVec01];"
          "vfmul.b %[xCu10], %[xSq10], %[aVec10];"
          "vfmul.b %[xCu11], %[xSq11], %[aVec11];"
          "vfmul.b %[xSq00], %[xSq00], %[vHalf];" // 0.5*x^2
          "vfmul.b %[xSq01], %[xSq01], %[vHalf];"
          "vfmul.b %[xSq10], %[xSq10], %[vHalf];"
          "vfmul.b %[xSq11], %[xSq11], %[vHalf];"
          "vfmul.b %[xCu00], %[xCu00], %[vSixth];" // 0.167*x^3
          "vfmul.b %[xCu01], %[xCu01], %[vSixth];"
          "vfmul.b %[xCu10], %[xCu10], %[vSixth];"
          "vfmul.b %[xCu11], %[xCu11], %[vSixth];"
          "vfmac.b %[xSq00], %[aVec00], %[vOne];" // 1*x + 0.5*x^2
          "vfmac.b %[xSq01], %[aVec01], %[vOne];"
          "vfmac.b %[xSq10], %[aVec10], %[vOne];"
          "vfmac.b %[xSq11], %[aVec11], %[vOne];"
          "vfadd.b %[xSq00], %[xSq00], %[vOne];" // 1 + 1*x + 0.5*x^2
          "vfadd.b %[xSq01], %[xSq01], %[vOne];"
          "vfadd.b %[xSq10], %[xSq10], %[vOne];"
          "vfadd.b %[xSq11], %[xSq11], %[vOne];"
          "vfadd.b %[xSq00], %[xSq00], %[xCu00];" // 1 + 1*x + 0.5*x^2 +
                                                  // 0.167*x^3
          "vfadd.b %[xSq01], %[xSq01], %[xCu01];"
          "vfadd.b %[xSq10], %[xSq10], %[xCu10];"
          "vfadd.b %[xSq11], %[xSq11], %[xCu11];"
          : [xSq00] "+&r"(exp00), [xSq01] "+&r"(exp01), [xSq10] "+&r"(exp10),
            [xSq11] "+&r"(exp11), [xCu00] "+&r"(max0), [xCu01] "+&r"(max1),
            [xCu10] "+&r"(xCu10), [xCu11] "+&r"(xCu11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11), [vSixth] "r"(vSixth), [vHalf] "r"(vHalf),
            [vOne] "r"(vOne));

      // Compute row-wise sum of all exponents
      asm volatile(
          "vfadd.b %[sum0], %[exp00], %[exp01];" // Use aVec00 as temporary sum
                                                 // variable
          "vfadd.b %[sum1], %[exp10], %[exp11];"
          "vfadd.b %[vSum0], %[vSum0], %[sum0];"
          "vfadd.b %[vSum1], %[vSum1], %[sum1];"
          : [vSum0] "+&r"(x0), [vSum1] "+&r"(x1), [sum0] "+&r"(aVec00),
            [sum1] "+&r"(aVec10)
          : [exp00] "r"(exp00), [exp01] "r"(exp01), [exp10] "r"(exp10),
            [exp11] "r"(exp11));

      // Store temporary variables
      (*(v4b *)&B[i * N + j]) = exp00;
      (*(v4b *)&B[i * N + j + 4]) = exp01;
      (*(v4b *)&B[(i + 1) * N + j]) = exp10;
      (*(v4b *)&B[(i + 1) * N + j + 4]) = exp11;
    }

    // Use x2, x3 as temporary sum variables
    v4b sum02, sum03;
    // Use vSixth, vHalf, vOne, max_init as temporary sum variables
    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.b %[sum00], %[vSum0], %[ShuffleMask0];"
        "pv.shuffle2.b %[sum01], %[vSum0], %[ShuffleMask1];"
        "pv.shuffle2.b %[sum02], %[vSum0], %[ShuffleMask2];"
        "pv.shuffle2.b %[sum03], %[vSum0], %[ShuffleMask3];"
        "pv.shuffle2.b %[sum10], %[vSum1], %[ShuffleMask0];"
        "pv.shuffle2.b %[sum11], %[vSum1], %[ShuffleMask1];"
        "pv.shuffle2.b %[sum12], %[vSum1], %[ShuffleMask2];"
        "pv.shuffle2.b %[sum13], %[vSum1], %[ShuffleMask3];"
        "vfadd.b %[vSum0], %[sum00], %[sum01];"
        "vfadd.b %[vSum1], %[sum10], %[sum11];"
        "vfadd.b %[vSum0], %[vSum0], %[sum02];"
        "vfadd.b %[vSum1], %[vSum1], %[sum12];"
        "vfadd.b %[vSum0], %[vSum0], %[sum03];"
        "vfadd.b %[vSum1], %[vSum1], %[sum13];"
        : [sum02] "+&r"(sum02), [sum03] "+&r"(sum03), [vSum0] "+&r"(x0),
          [vSum1] "+&r"(x1), [sum00] "+&r"(x2), [sum01] "+&r"(x3),
          [sum10] "+&r"(vSixth), [sum11] "+&r"(vHalf), [sum12] "+&r"(vOne),
          [sum13] "+&r"(max_init)
        : [ShuffleMask0] "r"(ShuffleMask0), [ShuffleMask1] "r"(ShuffleMask1),
          [ShuffleMask2] "r"(ShuffleMask2), [ShuffleMask3] "r"(ShuffleMask3));

    // 3) Divide by the row-wise sum
    for (j = 0; j < N; j += 8) {
      v4b bVec00 = *(v4b *)&(B[i * N + j]);
      v4b bVec01 = *(v4b *)&(B[i * N + j + 4]);
      v4b bVec10 = *(v4b *)&(B[(i + 1) * N + j]);
      v4b bVec11 = *(v4b *)&(B[(i + 1) * N + j + 4]);

      // Compute softmax = exp / sum_exp
      asm volatile("vfdiv.b %[bVec00], %[bVec00], %[vSum0];"
                   "vfdiv.b %[bVec01], %[bVec01], %[vSum0];"
                   "vfdiv.b %[bVec10], %[bVec10], %[vSum1];"
                   "vfdiv.b %[bVec11], %[bVec11], %[vSum1];"
                   : [bVec00] "+&r"(bVec00), [bVec01] "+&r"(bVec01),
                     [bVec10] "+&r"(bVec10), [bVec11] "+&r"(bVec11)
                   : [vSum0] "r"(x0), [vSum1] "r"(x1));

      (*(v4b *)&B[i * N + j]) = bVec00;
      (*(v4b *)&B[i * N + j + 4]) = bVec01;
      (*(v4b *)&B[(i + 1) * N + j]) = bVec10;
      (*(v4b *)&B[(i + 1) * N + j + 4]) = bVec11;
    }
  }
}
