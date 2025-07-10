// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library implements a normalization matrix based on the BatchNorm.
 * A is the M x N input matrix, B stores the normalized A matrix
 */

#pragma once
#include "builtins_v2.h"

void batchnorm_parallel_2x2_f16vec(const __fp16 *__restrict__ A,
                                   __fp16 *__restrict__ B, uint32_t M,
                                   uint32_t N, uint32_t core_id,
                                   uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  float InvM = 1.0f / (float)M;
  v2h vInvM;

  asm volatile("vfcpka.h.s %[vInvM], %[InvM], %[InvM];"
               : [vInvM] "+&r"(vInvM)
               : [InvM] "r"(InvM));

  for (j = core_id * 2; j < N; j += numThreads * 2) {

    v2h vSum = (v2h)0.0f;
    v2h vSumSq = (v2h)0.0f;

    for (i = 0; i < M; i += 2) {

      v2h aVec0 = *(v2h *)&(A[i * N + j]);
      v2h aVec1 = *(v2h *)&(A[(i + 1) * N + j]);

      v2h aVecSq0, aVecSq1;

      asm volatile(
          // Accumulate sum(x)
          "vfadd.h %[vSum], %[vSum], %[aVec0];"
          "vfmul.h %[aVecSq1], %[aVec1], %[aVec1];"
          "vfmul.h %[aVecSq0], %[aVec0], %[aVec0];"
          "vfadd.h %[vSum], %[vSum], %[aVec1];"
          // Accumulate sum(x^2)
          "vfadd.h %[vSumSq], %[vSumSq], %[aVecSq1];"
          "vfadd.h %[vSumSq], %[vSumSq], %[aVecSq0];"
          : [vSum] "+&r"(vSum), [vSumSq] "+&r"(vSumSq),
            [aVecSq0] "+&r"(aVecSq0), [aVecSq1] "+&r"(aVecSq1)
          : [aVec0] "r"(aVec0), [aVec1] "r"(aVec1));
    }

    v2h vMean, vVar, vStd, vMeanSq;

    asm volatile(
        // Compute the mean: mean = sum / M
        "vfmul.h %[vMean], %[vSum], %[vInvM];"
        // Compute E[x^2]
        "vfmul.h %[vVar], %[vSumSq], %[vInvM];"
        // Compute mean^2
        "vfmul.h %[vMeanSq], %[vMean], %[vMean];"
        // Compute the variance: var = E[x^2] - mean^2
        "vfsub.h %[vVar], %[vVar], %[vMeanSq];"
        // Compute the square root of Var: std = sqrt(var)
        "vfsqrt.h %[vStd], %[vVar];"
        : [vMean] "+&r"(vMean), [vVar] "+&r"(vVar), [vStd] "+&r"(vStd),
          [vInvM] "+&r"(vInvM), [vMeanSq] "+&r"(vMeanSq)
        : [vSum] "r"(vSum), [vSumSq] "r"(vSumSq));

    for (i = 0; i < M; i += 4) {

      v2h aVec0 = *(v2h *)&(A[i * N + j]);
      v2h aVec1 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec2 = *(v2h *)&(A[(i + 2) * N + j]);
      v2h aVec3 = *(v2h *)&(A[(i + 3) * N + j]);

      v2h aNorm0, aNorm1, aNorm2, aNorm3;

      asm volatile(
          // Compute: aVec0 - vMean
          "vfsub.h %[aNorm0], %[aVec0], %[vMean];"
          "vfsub.h %[aNorm1], %[aVec1], %[vMean];"
          "vfsub.h %[aNorm2], %[aVec2], %[vMean];"
          "vfsub.h %[aNorm3], %[aVec3], %[vMean];"
          // Compute: aNorm0 / vStd
          "vfdiv.h %[aNorm0], %[aNorm0], %[vStd];"
          "vfdiv.h %[aNorm1], %[aNorm1], %[vStd];"
          "vfdiv.h %[aNorm2], %[aNorm2], %[vStd];"
          "vfdiv.h %[aNorm3], %[aNorm3], %[vStd];"
          : [aNorm0] "+&r"(aNorm0), [aNorm1] "+&r"(aNorm1),
            [aNorm2] "+&r"(aNorm2), [aNorm3] "+&r"(aNorm3)
          : [aVec0] "r"(aVec0), [aVec1] "r"(aVec1), [aVec2] "r"(aVec2),
            [aVec3] "r"(aVec3), [vMean] "r"(vMean), [vStd] "r"(vStd));

      (*(v2h *)&B[i * N + j]) = aNorm0;
      (*(v2h *)&B[(i + 1) * N + j]) = aNorm1;
      (*(v2h *)&B[(i + 2) * N + j]) = aNorm2;
      (*(v2h *)&B[(i + 3) * N + j]) = aNorm3;
    }
  }
}
