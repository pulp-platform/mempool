// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library implements a normalization matrix based on the BatchNorm.
 * A is the M x N input matrix, B stores the normalized A matrix
 */

#pragma once
#include "builtins_v2.h"

void batchnorm_parallel_2x4_f8vec(const __fp8 *__restrict__ A,
                                  __fp8 *__restrict__ B, uint32_t M, uint32_t N,
                                  uint32_t core_id, uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  float InvM = 1.0f / (float)M;
  v4b vInvM;

  asm volatile("vfcpka.b.s %[vInvM], %[InvM], %[InvM];"
               "vfcpkb.b.s %[vInvM], %[InvM], %[InvM];"
               : [vInvM] "+&r"(vInvM)
               : [InvM] "r"(InvM));

  for (j = core_id * 4; j < N; j += numThreads * 4) {

    v4b vSum = (v4b)0.0f;
    v4b vSumSq = (v4b)0.0f;

    for (i = 0; i < M; i += 2) {

      v4b aVec0 = *(v4b *)&(A[i * N + j]);       // aVec0 = [a03 a02 a01 a00]
      v4b aVec1 = *(v4b *)&(A[(i + 1) * N + j]); // aVec1 = [a13 a12 a11 a10]

      v4b aVecSq0, aVecSq1;

      asm volatile(
          // Accumulate sum(x)
          "vfadd.b %[vSum], %[vSum], %[aVec0];"
          "vfmul.b %[aVecSq0], %[aVec0], %[aVec0];"
          "vfmul.b %[aVecSq1], %[aVec1], %[aVec1];"
          "vfadd.b %[vSum], %[vSum], %[aVec1];"
          // Accumulate sum(x^2)
          "vfadd.b %[vSumSq], %[vSumSq], %[aVecSq0];"
          "vfadd.b %[vSumSq], %[vSumSq], %[aVecSq1];"
          : [vSum] "+&r"(vSum), [vSumSq] "+&r"(vSumSq),
            [aVecSq0] "+&r"(aVecSq0), [aVecSq1] "+&r"(aVecSq1)
          : [aVec0] "r"(aVec0), [aVec1] "r"(aVec1));
    }

    v4b vMean, vVar, vStd, vMeanSq;

    asm volatile(
        // Compute the mean: mean = sum / M
        "vfmul.b %[vMean], %[vSum], %[vInvM];"
        // Compute E[x^2]
        "vfmul.b %[vVar], %[vSumSq], %[vInvM];"
        // Compute mean^2
        "vfmul.b %[vMeanSq], %[vMean], %[vMean];"
        // Compute the variance: var = E[x^2] - mean^2
        "vfsub.b %[vVar], %[vVar], %[vMeanSq];"
        // Compute the square root of Var: std = sqrt(var)
        "vfsqrt.b %[vStd], %[vVar];"
        : [vMean] "+&r"(vMean), [vVar] "+&r"(vVar), [vStd] "+&r"(vStd),
          [vMeanSq] "+&r"(vMeanSq)
        : [vSum] "r"(vSum), [vSumSq] "r"(vSumSq), [vInvM] "r"(vInvM));

    for (i = 0; i < M; i += 4) {

      v4b aVec0 = *(v4b *)&(A[i * N + j]);       // aVec0 = [a03 a02 a01 a00]
      v4b aVec1 = *(v4b *)&(A[(i + 1) * N + j]); // aVec1 = [a13 a12 a11 a10]
      v4b aVec2 = *(v4b *)&(A[(i + 2) * N + j]); // aVec2 = [a23 a22 a21 a20]
      v4b aVec3 = *(v4b *)&(A[(i + 3) * N + j]); // aVec3 = [a33 a32 a31 a30]

      v4b aNorm0, aNorm1, aNorm2, aNorm3;

      asm volatile(
          // Compute: aVec0 - vMean
          "vfsub.b %[aNorm0], %[aVec0], %[vMean];"
          "vfsub.b %[aNorm1], %[aVec1], %[vMean];"
          "vfsub.b %[aNorm2], %[aVec2], %[vMean];"
          "vfsub.b %[aNorm3], %[aVec3], %[vMean];"
          // Compute: aNorm0 / vStd
          "vfdiv.b %[aNorm0], %[aNorm0], %[vStd];"
          "vfdiv.b %[aNorm1], %[aNorm1], %[vStd];"
          "vfdiv.b %[aNorm2], %[aNorm2], %[vStd];"
          "vfdiv.b %[aNorm3], %[aNorm3], %[vStd];"
          : [aNorm0] "+&r"(aNorm0), [aNorm1] "+&r"(aNorm1),
            [aNorm2] "+&r"(aNorm2), [aNorm3] "+&r"(aNorm3)
          : [aVec0] "r"(aVec0), [aVec1] "r"(aVec1), [aVec2] "r"(aVec2),
            [aVec3] "r"(aVec3), [vMean] "r"(vMean), [vStd] "r"(vStd));

      (*(v4b *)&B[i * N + j]) = aNorm0;
      (*(v4b *)&B[(i + 1) * N + j]) = aNorm1;
      (*(v4b *)&B[(i + 2) * N + j]) = aNorm2;
      (*(v4b *)&B[(i + 3) * N + j]) = aNorm3;
    }
  }
}
