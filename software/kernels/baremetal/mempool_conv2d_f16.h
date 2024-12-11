// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

void conv2d_pointwise_f16s(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                           uint32_t matrix_N, uint32_t matrix_D,
                           uint32_t kernel_D) {

  uint32_t k, i, j, d;
  float sum;
  __fp16 sum_f16;
  v2h w, a;

  for (k = 0; k < kernel_D; k++) {
    for (i = 0; i < matrix_M; i++) {
      for (j = 0; j < matrix_N; j++) {

        sum = 0.0f;
        sum_f16 = (__fp16)0.0f;
        for (d = 0; d < matrix_D; d += 2) {

          // A and B are in C-like ordering, with the innermost dimension
          // changing faster W is in Fortran-like ordering, with the outermost
          // dimesion changing faster
          w = *(v2h *)&(W[k * matrix_D + d]);
          a = *(v2h *)&(A[i * matrix_N * matrix_D + j * matrix_D + d]);
          asm volatile("vfdotpex.s.h %[sum], %[a], %[w];"
                       : [sum] "+&r"(sum)
                       : [a] "r"(a), [w] "r"(w));
        }
        asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sum));
        B[i * matrix_N * kernel_D + j * kernel_D + k] = sum_f16;
      }
    }
  }
  return;
}

void conv2d_pointwise_f16s_unrolled4(__fp16 *A, __fp16 *B, __fp16 *W,
                                     uint32_t matrix_M, uint32_t matrix_N,
                                     uint32_t matrix_D, uint32_t kernel_D) {

  uint32_t k, i, j, d;
  float sum;
  __fp16 sum_f16;
  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;

  for (k = 0; k < kernel_D; k++) {
    for (i = 0; i < matrix_M; i++) {
      for (j = 0; j < matrix_N; j++) {

        sum = 0.0f;
        sum_f16 = (__fp16)0.0f;
        for (d = 0; d < matrix_D; d += 8) {

          // A and B are in C-like ordering, with the innermost dimension
          // changing faster W is in Fortran-like ordering, with the outermost
          // dimension changing faster
          w0 = *(v2h *)&(W[k * matrix_D + d + 0]);
          w1 = *(v2h *)&(W[k * matrix_D + d + 2]);
          w2 = *(v2h *)&(W[k * matrix_D + d + 4]);
          w3 = *(v2h *)&(W[k * matrix_D + d + 6]);

          a0 = *(v2h *)&(A[i * matrix_N * matrix_D + j * matrix_D + d + 0]);
          a1 = *(v2h *)&(A[i * matrix_N * matrix_D + j * matrix_D + d + 2]);
          a2 = *(v2h *)&(A[i * matrix_N * matrix_D + j * matrix_D + d + 4]);
          a3 = *(v2h *)&(A[i * matrix_N * matrix_D + j * matrix_D + d + 6]);

          asm volatile(
              "vfdotpex.s.h %[sum], %[a0], %[w0];"
              "vfdotpex.s.h %[sum], %[a1], %[w1];"
              "vfdotpex.s.h %[sum], %[a2], %[w2];"
              "vfdotpex.s.h %[sum], %[a3], %[w3];"
              : [sum] "+&r"(sum)
              : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),
                [w0] "r"(w0), [w1] "r"(w1), [w2] "r"(w2), [w3] "r"(w3));
        }
        asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sum));
        B[i * matrix_N * kernel_D + j * kernel_D + k] = sum_f16;
      }
    }
  }
  return;
}
