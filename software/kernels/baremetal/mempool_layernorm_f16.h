// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/* This library implements a normalization matrix based on the LayerNorm.
 * A is the M x N input matrix, B stores the normalized A matrix
 */

#pragma once
#include "builtins_v2.h"

void layernorm_parallel_2x4_f16vec(const __fp16 *__restrict__ A,
                                   __fp16 *__restrict__ B, uint32_t M,
                                   uint32_t N, uint32_t core_id,
                                   uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N

  float InvN = 1.0f / (float)N;
  v2h vInvN;

  asm volatile("vfcpka.h.s %[vInvN], %[InvN], %[InvN];"
               : [vInvN] "+&r"(vInvN)
               : [InvN] "r"(InvN));

  for (i = core_id * 2; i < M; i += numThreads * 2) {
    v2h vSumMean0 = (v2h)0.0f, vSumMean1 = (v2h)0.0f;
    v2h vSumSq0 = (v2h)0.0f, vSumSq1 = (v2h)0.0f;

    for (j = 0; j < N; j += 4) {
      v2h aVec00 = *(v2h *)&(A[i * N + j]);
      v2h aVec10 = *(v2h *)&(A[(i + 1) * N + j]);
      v2h aVec01 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);
      // Variables used to store square of loaded aVec01 and aVec11
      v2h aVecSq01, aVecSq11;
      asm volatile(
          // 1) Accumulate sum(x): Accumulate aVeci0 and aVeci1 in vSumi
          // 2) Accumulate sum(x^2): Square aVecji and then accumulate in
          // vSumSqi
          "vfadd.h %[vSum0], %[vSum0], %[aVec00];"
          "vfadd.h %[vSum1], %[vSum1], %[aVec10];"
          "vfmul.h %[aVec00], %[aVec00], %[aVec00];" // aVec00 stores square of
                                                     // loaded aVec00
          "vfmul.h %[aVec10], %[aVec10], %[aVec10];" // aVec10 stores square of
                                                     // loaded aVec10
          "vfmul.h %[aVecSq01], %[aVec01], %[aVec01];"
          "vfmul.h %[aVecSq11], %[aVec11], %[aVec11];"
          "vfadd.h %[vSumSq0], %[vSumSq0], %[aVec00];"
          "vfadd.h %[vSumSq1], %[vSumSq1], %[aVec10];"
          "vfadd.h %[vSum0], %[vSum0], %[aVec01];"
          "vfadd.h %[vSum1], %[vSum1], %[aVec11];"
          "vfadd.h %[vSumSq0], %[vSumSq0], %[aVecSq01];"
          "vfadd.h %[vSumSq1], %[vSumSq1], %[aVecSq11];"
          : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
            [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1),
            [aVecSq01] "+&r"(aVecSq01), [aVecSq11] "+&r"(aVecSq11)
          : [aVec00] "r"(aVec00), [aVec01] "r"(aVec01), [aVec10] "r"(aVec10),
            [aVec11] "r"(aVec11));
    }

    unsigned ShuffleMask = 0x00030002; // [a b] => [b a]
    // Variables used to store temporary sum values
    v2h x0, x1, y0, y1;
    // Reduce vector sum to one sum (replicated 2 times)
    asm volatile(
        "pv.shuffle2.h %[x0],      %[vSum0],   %[ShuffleMask];"
        "pv.shuffle2.h %[x1],      %[vSum1],   %[ShuffleMask];"
        "pv.shuffle2.h %[y0],      %[vSumSq0], %[ShuffleMask];"
        "pv.shuffle2.h %[y1],      %[vSumSq1], %[ShuffleMask];"
        "vfadd.h       %[vSum0],   %[vSum0],   %[x0];"
        "vfadd.h       %[vSum1],   %[vSum1],   %[x1];"
        "vfadd.h       %[vSumSq0], %[vSumSq0], %[y0];"
        "vfadd.h       %[vSumSq1], %[vSumSq1], %[y1];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [y0] "+&r"(y0), [y1] "+&r"(y1)
        : [ShuffleMask] "r"(ShuffleMask));

    // Compute variance
    asm volatile(
        // Compute E[x] = sum / N
        "vfmul.h  %[vSum0], %[vSum0], %[vInvN];"
        "vfmul.h  %[vSum1], %[vSum1], %[vInvN];"
        // Compute E[x^2] = sum^2 / N
        "vfmul.h  %[x0], %[vSumSq0], %[vInvN];"
        "vfmul.h  %[x1], %[vSumSq1], %[vInvN];"
        // Compute E[x]^2
        "vfmul.h  %[y0], %[vSum0], %[vSum0];"
        "vfmul.h  %[y1], %[vSum1], %[vSum1];"
        // Compute var = E[x^2] - E[x]^2
        "vfsub.h  %[x0], %[x0], %[y0];"
        "vfsub.h  %[x1], %[x1], %[y1];"
        // Compute the square root of Var: std = sqrt(var)
        // "vfsqrt.h      %[vSumSq0], %[x0];"
        // "vfsqrt.h      %[vSumSq1], %[x1];"
        : [vSum0] "+&r"(vSumMean0), [vSum1] "+&r"(vSumMean1),
          [vSumSq0] "+&r"(vSumSq0), [vSumSq1] "+&r"(vSumSq1), [x0] "+&r"(x0),
          [x1] "+&r"(x1), [y0] "+&r"(y0), [y1] "+&r"(y1)
        : [vInvN] "r"(vInvN));

    for (j = 0; j < N; j += 4) {
      // Variables used to store rows of matrix A: aVec00, ...
      v2h aVec00 = *(v2h *)&(A[i * N + j]); // aVec00 = [a03 a02 a01 a00]
      v2h aVec10 = *(v2h *)&(A[i * N + j + 2]);
      v2h aVec01 = *(v2h *)&(A[(i + 1) * N + j]); // aVec10 = [a13 a12 a11 a10]
      v2h aVec11 = *(v2h *)&(A[(i + 1) * N + j + 2]);
      asm volatile(
          // Compute: aVec0 - vMean
          "vfsub.h %[aVec00], %[aVec00], %[vMean0];"
          "vfsub.h %[aVec01], %[aVec01], %[vMean0];"
          "vfsub.h %[aVec10], %[aVec10], %[vMean1];"
          "vfsub.h %[aVec11], %[aVec11], %[vMean1];"
          // Compute: aNorm0 / vStd
          "vfdiv.h %[aVec00], %[aVec00], %[vStd0];"
          "vfdiv.h %[aVec01], %[aVec01], %[vStd0];"
          "vfdiv.h %[aVec10], %[aVec10], %[vStd1];"
          "vfdiv.h %[aVec11], %[aVec11], %[vStd1];"
          : [aVec00] "+r"(aVec00), [aVec01] "+r"(aVec01), [aVec10] "+r"(aVec10),
            [aVec11] "+r"(aVec11)
          : [vMean0] "r"(vSumMean0), [vMean1] "r"(vSumMean1),
            [vStd0] "r"(vSumSq0), [vStd1] "r"(vSumSq1));
      (*(v2h *)&B[i * N + j]) = aVec00;
      (*(v2h *)&B[i * N + j + 2]) = aVec10;
      (*(v2h *)&B[(i + 1) * N + j]) = aVec01;
      (*(v2h *)&B[(i + 1) * N + j + 2]) = aVec11;
    }
  }
}
