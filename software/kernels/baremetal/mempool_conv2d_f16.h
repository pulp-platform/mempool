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

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (k = 0; k < kernel_D; k++) {
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

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (k = 0; k < kernel_D; k++) {
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

void conv2d_depthwise_f16s(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                           uint32_t matrix_N, uint32_t matrix_D,
                           uint32_t kernel_K) {

  uint32_t i, j, d;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  v2h w, a, sum;

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (d = 0; d < matrix_D; d += 2) {
        sum = (v2h)0.0f;
        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            ia = (i - pad) + ik;
            ja = (j - pad) + jk;
            // skip (weights outside boundary)
            if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
              w = *(v2h *)&(W[ik * kernel_K * matrix_D + jk * matrix_D + d]);
              a = *(v2h *)&(A[ia * matrix_N * matrix_D + ja * matrix_D + d]);
              asm volatile("vfmac.h %[sum], %[a], %[w];"
                           : [sum] "+r"(sum)
                           : [a] "r"(a), [w] "r"(w));
            }
          }
        }
        *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d]) = sum;
      }
    }
  }

  return;
}

void conv2d_depthwise_f16s_unrolled4(__fp16 *A, __fp16 *B, __fp16 *W,
                                     uint32_t matrix_M, uint32_t matrix_N,
                                     uint32_t matrix_D, uint32_t kernel_K) {

  uint32_t i, j, d;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;
  v2h s0, s1, s2, s3;

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (d = 0; d < matrix_D; d += 8) {
        s0 = (v2h)0.0f;
        s1 = (v2h)0.0f;
        s2 = (v2h)0.0f;
        s3 = (v2h)0.0f;
        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            ia = (i - pad) + ik;
            ja = (j - pad) + jk;
            // skip (weights outside boundary)
            if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
              __fp16 *ptrW = W + ik * kernel_K * matrix_D + jk * matrix_D;
              __fp16 *ptrA = A + ia * matrix_N * matrix_D + ja * matrix_D;
              w0 = *(v2h *)&(ptrW[d]);
              w1 = *(v2h *)&(ptrW[d + 2]);
              w2 = *(v2h *)&(ptrW[d + 4]);
              w3 = *(v2h *)&(ptrW[d + 6]);
              a0 = *(v2h *)&(ptrA[d]);
              a1 = *(v2h *)&(ptrA[d + 2]);
              a2 = *(v2h *)&(ptrA[d + 4]);
              a3 = *(v2h *)&(ptrA[d + 6]);
              asm volatile(
                  "vfmac.h %[s0], %[a0], %[w0];"
                  "vfmac.h %[s1], %[a1], %[w1];"
                  "vfmac.h %[s2], %[a2], %[w2];"
                  "vfmac.h %[s3], %[a3], %[w3];"
                  : [s0] "+r"(s0), [s1] "+r"(s1), [s2] "+r"(s2), [s3] "+r"(s3)
                  : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),
                    [w0] "r"(w0), [w1] "r"(w1), [w2] "r"(w2), [w3] "r"(w3));
            }
          }
        }
        *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d]) = s0;
        *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d + 2]) = s1;
        *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d + 4]) = s2;
        *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d + 6]) = s3;
      }
    }
  }

  return;
}

void conv2d_depthwise_pointwise_f16s(__fp16 *A, __fp16 *B, __fp16 *Wd,
                                     __fp16 *Wp, uint32_t matrix_M,
                                     uint32_t matrix_N, uint32_t matrix_D,
                                     uint32_t kernel_K, uint32_t kernel_D) {

  uint32_t i, j, d, k;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  __fp16 sum_f16;
  float sp;
  v2h w, a, sd;

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (k = 0; k < kernel_D; k++) {
        sp = 0.0f;
        // Depthwise convolution
        for (d = 0; d < matrix_D; d += 2) {
          sd = (v2h)0.0f;
          for (ik = 0; ik < kernel_K; ik++) {
            for (jk = 0; jk < kernel_K; jk++) {
              ia = (i - pad) + ik;
              ja = (j - pad) + jk;
              // skip (weights outside boundary)
              if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) &&
                  (ja < matrix_N)) {
                w = *(v2h *)&(Wd[ik * kernel_K * matrix_D + jk * matrix_D + d]);
                a = *(v2h *)&(A[ia * matrix_N * matrix_D + ja * matrix_D + d]);
                asm volatile("vfmac.h %0, %1, %2;" : "+r"(sd) : "r"(a), "r"(w));
              }
            }
          }
          // Reduction with pointwise filter
          w = *(v2h *)&(Wp[k * matrix_D + d]);
          asm volatile("vfdotpex.s.h %0, %1, %2;"
                       : "+&r"(sp)
                       : "r"(sd), "r"(w));
        }
        asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sp));
        B[i * matrix_N * kernel_D + j * kernel_D + k] = sum_f16;
      }
    }
  }

  return;
}

void conv2d_depthwise_pointwise_f16s_unrolled4(__fp16 *A, __fp16 *B, __fp16 *Wd,
                                               __fp16 *Wp, uint32_t matrix_M,
                                               uint32_t matrix_N,
                                               uint32_t matrix_D,
                                               uint32_t kernel_K,
                                               uint32_t kernel_D) {

  uint32_t i, j, d, k;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  float sp;
  __fp16 sum_f16;
  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;
  v2h s0, s1, s2, s3;

  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      for (k = 0; k < kernel_D; k++) {
        sp = 0.0f;
        // Depthwise convolution
        for (d = 0; d < matrix_D; d += 8) {
          s0 = (v2h)0.0f;
          s1 = (v2h)0.0f;
          s2 = (v2h)0.0f;
          s3 = (v2h)0.0f;
          for (ik = 0; ik < kernel_K; ik++) {
            for (jk = 0; jk < kernel_K; jk++) {
              ia = (i - pad) + ik;
              ja = (j - pad) + jk;
              // skip (weights outside boundary)
              if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) &&
                  (ja < matrix_N)) {
                __fp16 *ptrW = &Wd[ik * kernel_K * matrix_D + jk * matrix_D];
                __fp16 *ptrA = &A[ia * matrix_N * matrix_D + ja * matrix_D];
                w0 = *(v2h *)&(ptrW[d]);
                w1 = *(v2h *)&(ptrW[d + 2]);
                w2 = *(v2h *)&(ptrW[d + 4]);
                w3 = *(v2h *)&(ptrW[d + 6]);
                a0 = *(v2h *)&(ptrA[d]);
                a1 = *(v2h *)&(ptrA[d + 2]);
                a2 = *(v2h *)&(ptrA[d + 4]);
                a3 = *(v2h *)&(ptrA[d + 6]);
                asm volatile(
                    "vfmac.h %[s0], %[a0], %[w0];"
                    "vfmac.h %[s1], %[a1], %[w1];"
                    "vfmac.h %[s2], %[a2], %[w2];"
                    "vfmac.h %[s3], %[a3], %[w3];"
                    : [s0] "+r"(s0), [s1] "+r"(s1), [s2] "+r"(s2), [s3] "+r"(s3)
                    : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),
                      [w0] "r"(w0), [w1] "r"(w1), [w2] "r"(w2), [w3] "r"(w3));
              }
            }
          }
          // Pointwise reduction
          w0 = *(v2h *)&(Wp[k * matrix_D + d + 0]);
          w1 = *(v2h *)&(Wp[k * matrix_D + d + 2]);
          w2 = *(v2h *)&(Wp[k * matrix_D + d + 4]);
          w3 = *(v2h *)&(Wp[k * matrix_D + d + 6]);
          asm volatile("vfdotpex.s.h %0, %1, %2;"
                       : "+&r"(sp)
                       : "r"(s0), "r"(w0));
          asm volatile("vfdotpex.s.h %0, %1, %2;"
                       : "+&r"(sp)
                       : "r"(s1), "r"(w1));
          asm volatile("vfdotpex.s.h %0, %1, %2;"
                       : "+&r"(sp)
                       : "r"(s2), "r"(w2));
          asm volatile("vfdotpex.s.h %0, %1, %2;"
                       : "+&r"(sp)
                       : "r"(s3), "r"(w3));
        }
        asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sp));
        B[i * matrix_N * kernel_D + j * kernel_D + k] = sum_f16;
      }
    }
  }

  return;
}
