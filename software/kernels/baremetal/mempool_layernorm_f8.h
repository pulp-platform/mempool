// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library implements a normalization matrix based on the LayerNorm.
 * A is the M x N input matrix, B stores the normalized A matrix
 */

#pragma once
#include "builtins_v2.h"

void layernorm_parallel_2x8_f8vec(const __fp8 *__restrict__ A,
                                  __fp8 *__restrict__ B, uint32_t M, uint32_t N,
                                  uint32_t core_id, uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  float InvN = 1.0f / (float)N;
  v4b vInvN;

  asm volatile("vfcpka.b.s %[vInvN], %[InvN], %[InvN];"
               "vfcpkb.b.s %[vInvN], %[InvN], %[InvN];"
               : [vInvN] "+&r"(vInvN)
               : [InvN] "r"(InvN));

  for (i = core_id * 2; i < M; i += numThreads * 2) {

    v4b vSumMean0 = (v4b)0.0f, vSumMean1 = (v4b)0.0f;
    v4b vSumSq0 = (v4b)0.0f, vSumSq1 = (v4b)0.0f;

    for (j = 0; j < N; j += 8) {

      v4b aVec00 = *(v4b *)&(A[i * N + j]);       // aVec0 = [a03 a02 a01 a00]
      v4b aVec10 = *(v4b *)&(A[(i + 1) * N + j]); // aVec1 = [a13 a12 a11 a10]
      v4b aVec01 = *(v4b *)&(A[i * N + j + 4]);
      v4b aVec11 = *(v4b *)&(A[(i + 1) * N + j + 4]);

      v4b aVecSq01, aVecSq11;

      asm volatile(
          // 1) Accumulate sum(x): Accumulate aVeci0 and aVeci1 in vSumi
          // 2) Accumulate sum(x^2): Square aVecji and then accumulate in
          // vSumSqi
          "vfadd.b %[vSum0], %[vSum0], %[aVec00];"
          "vfadd.b %[vSum1], %[vSum1], %[aVec10];"
          "vfmul.b %[aVec00], %[aVec00], %[aVec00];" // aVec00 stores square of
                                                     // loaded aVec00
          "vfmul.b %[aVec10], %[aVec10], %[aVec10];" // aVec10 stores square of
                                                     // loaded aVec10
          "vfmul.b %[aVecSq01], %[aVec01], %[aVec01];"
          "vfmul.b %[aVecSq11], %[aVec11], %[aVec11];"
          "vfadd.b %[vSumSq0], %[vSumSq0], %[aVec00];"
          "vfadd.b %[vSumSq1], %[vSumSq1], %[aVec10];"
          "vfadd.b %[vSum0], %[vSum0], %[aVec01];"
          "vfadd.b %[vSum1], %[vSum1], %[aVec11];"
          "vfadd.b %[vSumSq0], %[vSumSq0], %[aVecSq01];"
          "vfadd.b %[vSumSq1], %[vSumSq1], %[aVecSq11];"
          : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
            [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1),
            [aVecSq01] "+&r"(aVecSq01), [aVecSq11] "+&r"(aVecSq11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    unsigned ShuffleMask0 = 0x04040404; // [a b c d] => [d d d d]
    unsigned ShuffleMask1 = 0x05050505; // [a b c d] => [c c c c]
    unsigned ShuffleMask2 = 0x06060606; // [a b c d] => [b b b b]
    unsigned ShuffleMask3 = 0x07070707; // [a b c d] => [a a a a]
    // Variables used to store temporary sum values
    v4b x0, x1, x2, x3; // used as sum00, ...
    v4b y0, y1, y2, y3;
    v4b temp0, temp1;
    // Reduce vector sum to one sum (replicated 4 times)
    asm volatile(
        // Broadcast each element across vector lanes for full reduction
        "pv.shuffle2.b %[x0], %[vSum0], %[ShuffleMask0];"
        "pv.shuffle2.b %[x1], %[vSum0], %[ShuffleMask1];"
        "pv.shuffle2.b %[x2], %[vSum1], %[ShuffleMask0];"
        "pv.shuffle2.b %[x3], %[vSum1], %[ShuffleMask1];"
        "pv.shuffle2.b %[y0], %[vSumSq0], %[ShuffleMask0];"
        "pv.shuffle2.b %[y1], %[vSumSq0], %[ShuffleMask1];"
        "pv.shuffle2.b %[y2], %[vSumSq1], %[ShuffleMask0];"
        "pv.shuffle2.b %[y3], %[vSumSq1], %[ShuffleMask1];"
        "vfadd.b %[ShuffleMask0], %[x0], %[x1];" // Use ShuffleMask as temp
                                                 // storage
        "vfadd.b %[ShuffleMask1], %[x2], %[x3];"
        "vfadd.b %[temp0], %[y0], %[y1];"
        "vfadd.b %[temp1], %[y2], %[y3];"

        "pv.shuffle2.b %[x0], %[vSum0], %[ShuffleMask2];"
        "pv.shuffle2.b %[x1], %[vSum0], %[ShuffleMask3];"
        "pv.shuffle2.b %[x2], %[vSum1], %[ShuffleMask2];"
        "pv.shuffle2.b %[x3], %[vSum1], %[ShuffleMask3];"
        "pv.shuffle2.b %[y0], %[vSumSq0], %[ShuffleMask2];"
        "pv.shuffle2.b %[y1], %[vSumSq0], %[ShuffleMask3];"
        "pv.shuffle2.b %[y2], %[vSumSq1], %[ShuffleMask2];"
        "pv.shuffle2.b %[y3], %[vSumSq1], %[ShuffleMask3];"
        "vfadd.b %[vSum0], %[ShuffleMask0], %[x0];"
        "vfadd.b %[vSum1], %[ShuffleMask1], %[x2];"
        "vfadd.b %[vSumSq0], %[temp0], %[y0];"
        "vfadd.b %[vSumSq1], %[temp1], %[y2];"
        "vfadd.b %[vSum0], %[vSum0], %[x1];"
        "vfadd.b %[vSum1], %[vSum1], %[x3];"
        "vfadd.b %[vSumSq0], %[vSumSq0], %[y1];"
        "vfadd.b %[vSumSq1], %[vSumSq1], %[y3];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [x2] "+&r"(x2), [x3] "+&r"(x3), [y0] "+&r"(y0),
          [y1] "+&r"(y1), [y2] "+&r"(y2), [y3] "+&r"(y3),
          [ShuffleMask0] "+&r"(ShuffleMask0),
          [ShuffleMask1] "+&r"(ShuffleMask1), [temp0] "+&r"(temp0),
          [temp1] "+&r"(temp1)
        : [ShuffleMask2] "r"(ShuffleMask2), [ShuffleMask3] "r"(ShuffleMask3));

    asm volatile(
        // Compute the mean: mean = sum / N
        "vfmul.b %[vSum0], %[vSum0], %[vInvN];" // vSum0 stores vMean0
        "vfmul.b %[vSum1], %[vSum1], %[vInvN];"
        // Compute E[x^2]
        "vfmul.b %[x0], %[vSumSq0], %[vInvN];"
        "vfmul.b %[x1], %[vSumSq1], %[vInvN];"
        // Compute mean^2
        "vfmul.b %[vSumSq0], %[vSum0], %[vSum0];"
        "vfmul.b %[vSumSq1], %[vSum1], %[vSum1];"
        // Compute the variance: var = E[x^2] - mean^2
        "vfsub.b %[x0], %[x0], %[vSumSq0];"
        "vfsub.b %[x1], %[x1], %[vSumSq1];"
        // Compute the square root of Var: std = sqrt(var)
        "vfsqrt.b %[vSumSq0], %[x0];"
        "vfsqrt.b %[vSumSq1], %[x1];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [x2] "+&r"(x2), [x3] "+&r"(x3)
        : [vInvN] "r"(vInvN));

    for (j = 0; j < N; j += 8) {

      x0 = *(v4b *)&(A[i * N + j]); // aVec0 = [a03 a02 a01 a00]
      x1 = *(v4b *)&(A[i * N + j + 4]);
      x2 = *(v4b *)&(A[(i + 1) * N + j]); // aVec1 = [a13 a12 a11 a10]
      x3 = *(v4b *)&(A[(i + 1) * N + j + 4]);

      asm volatile(
          // Compute: aVec0 - vMean
          "vfsub.b %[aVec00], %[aVec00], %[vMean0];"
          "vfsub.b %[aVec01], %[aVec01], %[vMean0];"
          "vfsub.b %[aVec10], %[aVec10], %[vMean1];"
          "vfsub.b %[aVec11], %[aVec11], %[vMean1];"
          // Compute: aNorm0 / vStd
          "vfdiv.b %[aVec00], %[aVec00], %[vStd0];"
          "vfdiv.b %[aVec01], %[aVec01], %[vStd0];"
          "vfdiv.b %[aVec10], %[aVec10], %[vStd1];"
          "vfdiv.b %[aVec11], %[aVec11], %[vStd1];"
          : [aVec00] "+&r"(x0), [aVec01] "+&r"(x1), [aVec10] "+&r"(x2),
            [aVec11] "+&r"(x3)
          : [vMean0] "r"(vSumMean0), [vMean1] "r"(vSumMean0),
            [vStd0] "r"(vSumSq0), [vStd1] "r"(vSumSq1));

      (*(v4b *)&B[i * N + j]) = x0;
      (*(v4b *)&B[i * N + j + 4]) = x1;
      (*(v4b *)&B[(i + 1) * N + j]) = x2;
      (*(v4b *)&B[(i + 1) * N + j + 4]) = x3;
    }
  }
}
