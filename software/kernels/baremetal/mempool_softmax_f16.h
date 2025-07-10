// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library applies a softmax over an entire matrix.
 * A is the M x N input matrix, B stores the resulting matrix
 */

#pragma once
#include "builtins_v2.h"

void softmax_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                 __fp16 *__restrict__ B, uint32_t M, uint32_t N,
                                 uint32_t core_id, uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  const unsigned ShuffleMask1 = 0x00020002; // [a b] => [a a]
  const unsigned ShuffleMask0 = 0x00030003; // [a b] => [b b]

  float Sixth = 0.167f;
  float Half = 0.5f;
  float One = 1.0f;
  float init = 0.5f;
  v2h vSixth, vHalf, vOne, max_init;
  asm volatile(
      "vfcpka.h.s %[vSixth], %[Sixth], %[Sixth];"
      "vfcpka.h.s %[vHalf], %[Half], %[Half];"
      "vfcpka.h.s %[vOne], %[One], %[One];"
      "vfcpka.h.s %[max_init], %[init], %[init];"
      : [vSixth] "+&r"(vSixth), [vHalf] "+&r"(vHalf), [vOne] "+&r"(vOne),
        [max_init] "+&r"(max_init)
      : [Sixth] "r"(Sixth), [Half] "r"(Half), [One] "r"(One), [init] "r"(init));

  for (i = core_id * 2; i < M; i += numThreads * 2) {

    // 1) Find the row-wise maximum value
    v2h max0 = max_init;
    v2h max1 = max_init;

    for (j = 0; j < N; j += 4) {

      v2h aVec00 = *(v2h *)&(A[i * N + j]);           // aVec00 = [a01 a00]
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);       // aVec01 = [a03 a02]
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);     // aVec10 = [a11 a10]
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]); // aVec11 = [a13 a12]

      v2h temp0, temp1;

      asm volatile(
          // Find max value (no full reduction)
          "vfmax.h %[temp0], %[aVec00], %[aVec01];"
          "vfmax.h %[temp1], %[aVec10], %[aVec11];"
          "vfmax.h %[max0], %[max0], %[temp0];"
          "vfmax.h %[max1], %[max1], %[temp1];"
          : [max0] "+&r"(max0), [max1] "+&r"(max1), [temp0] "+&r"(temp0),
            [temp1] "+&r"(temp1)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    // Potential max elements:
    v2h x0, x1, x2, x3;

    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.h %[pmax00], %[max0], %[ShuffleMask0];"
        "pv.shuffle2.h %[pmax01], %[max0], %[ShuffleMask1];"
        "pv.shuffle2.h %[pmax10], %[max1], %[ShuffleMask0];"
        "pv.shuffle2.h %[pmax11], %[max1], %[ShuffleMask1];"
        "vfmax.h %[max0], %[pmax00], %[pmax01];"
        "vfmax.h %[max1], %[pmax10], %[pmax11];"
        : [max0] "+&r"(max0), [max1] "+&r"(max1), [pmax00] "+&r"(x0),
          [pmax01] "+&r"(x1), [pmax10] "+&r"(x2), [pmax11] "+&r"(x3)
        : [ShuffleMask0] "r"(ShuffleMask0), [ShuffleMask1] "r"(ShuffleMask1));

    // 2) Compute exp(x - max)
    // Store sum value in x0, x1
    x0 = (v2h)0.0f;
    x1 = (v2h)0.0f;

    for (j = 0; j < N; j += 4) {

      v2h aVec00 = *(v2h *)&(A[i * N + j]);
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);

      // Compute x' = x - max(x)
      asm volatile("vfsub.h %[aVec00], %[aVec00], %[max0];"
                   "vfsub.h %[aVec01], %[aVec01], %[max0];"
                   "vfsub.h %[aVec10], %[aVec10], %[max1];"
                   "vfsub.h %[aVec11], %[aVec11], %[max1];"
                   : [aVec00] "+&r"(aVec00), [aVec01] "+&r"(aVec01),
                     [aVec10] "+&r"(aVec10), [aVec11] "+&r"(aVec11)
                   : [max0] "r"(max0), [max1] "r"(max1));

      v2h xCu10, xCu11;
      v2h exp00, exp01, exp10, exp11;

      // Approximate exp with Taylor Series
      asm volatile(
          "vfmul.h %[xSq00], %[aVec00], %[aVec00];" // x^2
          "vfmul.h %[xSq01], %[aVec01], %[aVec01];"
          "vfmul.h %[xSq10], %[aVec10], %[aVec10];"
          "vfmul.h %[xSq11], %[aVec11], %[aVec11];"
          "vfmul.h %[xCu00], %[xSq00], %[aVec00];" // x^3
          "vfmul.h %[xCu01], %[xSq01], %[aVec01];"
          "vfmul.h %[xCu10], %[xSq10], %[aVec10];"
          "vfmul.h %[xCu11], %[xSq11], %[aVec11];"
          "vfmul.h %[xSq00], %[xSq00], %[vHalf];" // 0.5*x^2
          "vfmul.h %[xSq01], %[xSq01], %[vHalf];"
          "vfmul.h %[xSq10], %[xSq10], %[vHalf];"
          "vfmul.h %[xSq11], %[xSq11], %[vHalf];"
          "vfmul.h %[xCu00], %[xCu00], %[vSixth];" // 0.167*x^3
          "vfmul.h %[xCu01], %[xCu01], %[vSixth];"
          "vfmul.h %[xCu10], %[xCu10], %[vSixth];"
          "vfmul.h %[xCu11], %[xCu11], %[vSixth];"
          "vfmac.h %[xSq00], %[aVec00], %[vOne];" // 1*x + 0.5*x^2
          "vfmac.h %[xSq01], %[aVec01], %[vOne];"
          "vfmac.h %[xSq10], %[aVec10], %[vOne];"
          "vfmac.h %[xSq11], %[aVec11], %[vOne];"
          "vfadd.h %[xSq00], %[xSq00], %[vOne];" // 1 + 1*x + 0.5*x^2
          "vfadd.h %[xSq01], %[xSq01], %[vOne];"
          "vfadd.h %[xSq10], %[xSq10], %[vOne];"
          "vfadd.h %[xSq11], %[xSq11], %[vOne];"
          "vfadd.h %[xSq00], %[xSq00], %[xCu00];" // 1 + 1*x + 0.5*x^2 +
                                                  // 0.167*x^3
          "vfadd.h %[xSq01], %[xSq01], %[xCu01];"
          "vfadd.h %[xSq10], %[xSq10], %[xCu10];"
          "vfadd.h %[xSq11], %[xSq11], %[xCu11];"
          : [xSq00] "+&r"(exp00), [xSq01] "+&r"(exp01), [xSq10] "+&r"(exp10),
            [xSq11] "+&r"(exp11), [vSum0] "+&r"(x0), [vSum1] "+&r"(x1),
            [xCu00] "+&r"(max0), [xCu01] "+&r"(max1), [xCu10] "+&r"(xCu10),
            [xCu11] "+&r"(xCu11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11), [vSixth] "r"(vSixth), [vHalf] "r"(vHalf),
            [vOne] "r"(vOne));

      // Compute row-wise sum of all exponents
      asm volatile(
          "vfadd.h %[sum0], %[exp00], %[exp01];" // Use aVec00 as temporary sum
                                                 // variable
          "vfadd.h %[sum1], %[exp10], %[exp11];"
          "vfadd.h %[vSum0], %[vSum0], %[sum0];"
          "vfadd.h %[vSum1], %[vSum1], %[sum1];"
          : [vSum0] "+&r"(x0), [vSum1] "+&r"(x1), [sum0] "+&r"(aVec00),
            [sum1] "+&r"(aVec10)
          : [exp00] "r"(exp00), [exp01] "r"(exp01), [exp10] "r"(exp10),
            [exp11] "r"(exp11));

      // Store temporary variables
      (*(v2h *)&B[i * N + j]) = exp00;
      (*(v2h *)&B[i * N + j + 2]) = exp01;
      (*(v2h *)&B[(i + 1) * N + j]) = exp10;
      (*(v2h *)&B[(i + 1) * N + j + 2]) = exp11;
    }

    // Use x2, x3 and vHalf, vOne as temporary sum variables
    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.h %[sum00], %[vSum0], %[ShuffleMask0];"
        "pv.shuffle2.h %[sum01], %[vSum0], %[ShuffleMask1];"
        "pv.shuffle2.h %[sum10], %[vSum1], %[ShuffleMask0];"
        "pv.shuffle2.h %[sum11], %[vSum1], %[ShuffleMask1];"
        "vfadd.h %[vSum0], %[sum00], %[sum01];"
        "vfadd.h %[vSum1], %[sum10], %[sum11];"
        : [vSum0] "+&r"(x0), [vSum1] "+&r"(x1), [sum00] "+&r"(x2),
          [sum01] "+&r"(x3), [sum10] "+&r"(vHalf), [sum11] "+&r"(vOne)
        : [ShuffleMask0] "r"(ShuffleMask0), [ShuffleMask1] "r"(ShuffleMask1));

    // 3) Divide by the row-wise sum
    for (j = 0; j < N; j += 4) {
      v2h bVec00 = *(v2h *)&(B[i * N + j]);
      v2h bVec01 = *(v2h *)&(B[i * N + j + 2]);
      v2h bVec10 = *(v2h *)&(B[(i + 1) * N + j]);
      v2h bVec11 = *(v2h *)&(B[(i + 1) * N + j + 2]);

      // v2h res00, res01, res10, res11;
      //  Compute softmax = exp / sum_exp
      asm volatile("vfdiv.h %[bVec00], %[bVec00], %[vSum0];"
                   "vfdiv.h %[bVec01], %[bVec01], %[vSum0];"
                   "vfdiv.h %[bVec10], %[bVec10], %[vSum1];"
                   "vfdiv.h %[bVec11], %[bVec11], %[vSum1];"
                   : [bVec00] "+&r"(bVec00), [bVec01] "+&r"(bVec01),
                     [bVec10] "+&r"(bVec10), [bVec11] "+&r"(bVec11)
                   : [vSum0] "r"(x0), [vSum1] "r"(x1));

      (*(v2h *)&B[i * N + j]) = bVec00;
      (*(v2h *)&B[i * N + j + 2]) = bVec01;
      (*(v2h *)&B[(i + 1) * N + j]) = bVec10;
      (*(v2h *)&B[(i + 1) * N + j + 2]) = bVec11;
    }
  }
}
