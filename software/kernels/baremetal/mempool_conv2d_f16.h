// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"
#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (true)

void conv2d_pointwise_f16(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                          uint32_t matrix_N, uint32_t matrix_D,
                          uint32_t kernel_D,
                          uint32_t __attribute__((unused)) core_id,
                          uint32_t __attribute__((unused)) numThreads) {

#if NUM_REDMULE_TILES > 0
  uint32_t M = matrix_M * matrix_N;
  redmule_asynch_parallel(A, W, B, M, matrix_D, kernel_D, GEMM, SHIFT,
                          PORT_WIDTH);
  wait_redmule();
#else
  uint32_t k, i, d;
  float sum;
  __fp16 sum_f16;
  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;

  for (i = core_id; i < matrix_M * matrix_N; i += numThreads) {
    for (k = 0; k < kernel_D; k++) {
      sum = 0.0f;
      sum_f16 = (__fp16)0.0f;

      /* main loop: handle blocks of 8 channels (unroll factor 4) */
      for (d = 0; d + 8 <= matrix_D; d += 8) {
        w0 = *(v2h *)&(W[k * matrix_D + d + 0]);
        w1 = *(v2h *)&(W[k * matrix_D + d + 2]);
        w2 = *(v2h *)&(W[k * matrix_D + d + 4]);
        w3 = *(v2h *)&(W[k * matrix_D + d + 6]);
        a0 = *(v2h *)&(A[i * matrix_D + d + 0]);
        a1 = *(v2h *)&(A[i * matrix_D + d + 2]);
        a2 = *(v2h *)&(A[i * matrix_D + d + 4]);
        a3 = *(v2h *)&(A[i * matrix_D + d + 6]);

        asm volatile("vfdotpex.s.h %[sum], %[a0], %[w0];"
                     "vfdotpex.s.h %[sum], %[a1], %[w1];"
                     "vfdotpex.s.h %[sum], %[a2], %[w2];"
                     "vfdotpex.s.h %[sum], %[a3], %[w3];"
                     : [sum] "+&r"(sum)
                     : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),
                       [w0] "r"(w0), [w1] "r"(w1), [w2] "r"(w2), [w3] "r"(w3));
      }

      /* tail: any remaining 1‑vector (2 channels) segments */
      for (; d < matrix_D; d += 2) {
        w0 = *(v2h *)&(W[k * matrix_D + d]);
        a0 = *(v2h *)&(A[i * matrix_D + d]);
        asm volatile("vfdotpex.s.h %[sum], %[a0], %[w0];"
                     : [sum] "+&r"(sum)
                     : [a0] "r"(a0), [w0] "r"(w0));
      }

      asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sum));
      B[i * kernel_D + k] = sum_f16;
    }
  }
#endif
  return;
}

#define CONV_DEPTHWISE_LOOP4()                                                 \
  v2h w0, w1, w2, w3;                                                          \
  v2h a0, a1, a2, a3;                                                          \
  asm volatile(                                                                \
      "lw %[w0], 0(%[addr_w]);"                                                \
      "lw %[w1], 4(%[addr_w]);"                                                \
      "lw %[w2], 8(%[addr_w]);"                                                \
      "lw %[w3],12(%[addr_w]);"                                                \
      "lw %[a0], 0(%[addr_a]);"                                                \
      "lw %[a1], 4(%[addr_a]);"                                                \
      "lw %[a2], 8(%[addr_a]);"                                                \
      "lw %[a3],12(%[addr_a]);"                                                \
      "vfmac.h %[s0], %[a0], %[w0];"                                           \
      "vfmac.h %[s1], %[a1], %[w1];"                                           \
      "vfmac.h %[s2], %[a2], %[w2];"                                           \
      "vfmac.h %[s3], %[a3], %[w3];"                                           \
      : [s0] "+r"(s0), [s1] "+r"(s1), [s2] "+r"(s2), [s3] "+r"(s3),            \
        [a0] "=&r"(a0), [a1] "=&r"(a1), [a2] "=&r"(a2), [a3] "=&r"(a3),        \
        [w0] "=&r"(w0), [w1] "=&r"(w1), [w2] "=&r"(w2), [w3] "=&r"(w3),        \
        [addr_a] "+&r"(ptrA), [addr_w] "+&r"(ptrW)                             \
      :                                                                        \
      : "memory");

void conv2d_depthwise_f16(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                          uint32_t matrix_N, uint32_t matrix_D,
                          uint32_t kernel_K, uint32_t core_id,
                          uint32_t numThreads) {

  uint32_t ij, i, j, k, d;
  uint32_t pad = kernel_K / 2;
  uint32_t ik, jk;
  uint32_t idx_a;
  uint32_t offset;

  __fp16 *ptrA, *ptrW, *ptrB;
  v2h s0, s1, s2, s3;

  const uint32_t ND = matrix_N * matrix_D;
  const uint32_t KD = kernel_K * matrix_D;
  const uint32_t MND = matrix_M * ND;
  bool notboundary;

  k = 16 * core_id;
  while (k < MND) {
    for (offset = 0; offset <= 8; offset += 8) {
      // Loop indeces
      ij = (k + offset) / matrix_D;
      i = ij / matrix_N;
      j = ij % matrix_N;
      d = (k + offset) % matrix_D;

      // Accumulators
      s0 = (v2h)0.0f;
      s1 = (v2h)0.0f;
      s2 = (v2h)0.0f;
      s3 = (v2h)0.0f;

      // Padding
      notboundary = (i >= pad);
      notboundary &= (j >= pad);
      notboundary &= (i < matrix_M - pad);
      notboundary &= (j < matrix_N - pad);

      if (notboundary) {
        idx_a = d + i * ND + j * matrix_D;
        idx_a -= pad * (ND + matrix_D);
        ptrA = &A[idx_a];
        ptrW = &W[d];

        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            CONV_DEPTHWISE_LOOP4();
            ptrW += matrix_D;
            ptrA += matrix_D;
          }
          ptrA += ND - KD;
        }
      }
      ptrB = &B[i * ND + j * matrix_D + d];
      *((v2h *)&ptrB[0]) = s0;
      *((v2h *)&ptrB[2]) = s1;
      *((v2h *)&ptrB[4]) = s2;
      *((v2h *)&ptrB[6]) = s3;
    }

    // Pointer increment
    k += 16 * numThreads;
  }
  return;
}

void conv2d_depthwise_pointwise_f16(__fp16 *A, __fp16 *B, __fp16 *Wd,
                                    __fp16 *Wp, uint32_t matrix_M,
                                    uint32_t matrix_N, uint32_t matrix_D,
                                    uint32_t kernel_K, uint32_t kernel_D,
                                    uint32_t core_id, uint32_t numThreads) {

  uint32_t l, i, j, d, k;
  uint32_t ik, jk;
  uint32_t pad = kernel_K / 2;
  const uint32_t image_row_stride = matrix_N * matrix_D;
  const uint32_t kernel_row_stride = kernel_K * matrix_D;
  __fp16 sum_f16;
  float sp;

  for (l = core_id; l < matrix_M * matrix_N; l += numThreads) {
    i = l / matrix_N;
    j = l % matrix_N;
    int32_t i_signed = (int32_t)i;
    int32_t j_signed = (int32_t)j;
    int32_t ia_start = i_signed - (int32_t)pad;
    int32_t ja_start = j_signed - (int32_t)pad;
    int32_t ia_limit = ia_start + (int32_t)kernel_K;
    int32_t ja_limit = ja_start + (int32_t)kernel_K;
    int interior = (ia_start >= 0) && (ja_start >= 0) &&
                   (ia_limit <= (int32_t)matrix_M) &&
                   (ja_limit <= (int32_t)matrix_N);
    uint32_t interior_base = 0;
    if (interior) {
      interior_base =
          ((uint32_t)ia_start * matrix_N + (uint32_t)ja_start) * matrix_D;
    }

    for (k = 0; k < kernel_D; k++) {
      sp = 0.0f;

      /* unrolled 8-channel chunks */
      for (d = 0; d + 8 <= matrix_D; d += 8) {
        v2h s0 = (v2h)0.0f, s1 = (v2h)0.0f, s2 = (v2h)0.0f, s3 = (v2h)0.0f;
        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            uint32_t kernel_base = ik * kernel_row_stride + jk * matrix_D;
            __fp16 *ptrW = (__fp16 *)0;
            __fp16 *ptrA = (__fp16 *)0;
            if (interior) {
              ptrW = &Wd[kernel_base + d];
              ptrA =
                  &A[interior_base + ik * image_row_stride + jk * matrix_D + d];
            } else {
              int32_t ia = ia_start + (int32_t)ik;
              int32_t ja = ja_start + (int32_t)jk;
              if ((ia >= 0) && (ja >= 0) && (ia < (int32_t)matrix_M) &&
                  (ja < (int32_t)matrix_N)) {
                ptrW = &Wd[kernel_base + d];
                ptrA = &A[(uint32_t)ia * image_row_stride +
                          (uint32_t)ja * matrix_D + d];
              }
            }
            if (ptrW && ptrA) {
              CONV_DEPTHWISE_LOOP4();
            }
          }
        }
        v2h w0 = *(v2h *)&(Wp[k * matrix_D + d + 0]);
        v2h w1 = *(v2h *)&(Wp[k * matrix_D + d + 2]);
        v2h w2 = *(v2h *)&(Wp[k * matrix_D + d + 4]);
        v2h w3 = *(v2h *)&(Wp[k * matrix_D + d + 6]);
        asm volatile("vfdotpex.s.h %0, %1, %2;" : "+&r"(sp) : "r"(s0), "r"(w0));
        asm volatile("vfdotpex.s.h %0, %1, %2;" : "+&r"(sp) : "r"(s1), "r"(w1));
        asm volatile("vfdotpex.s.h %0, %1, %2;" : "+&r"(sp) : "r"(s2), "r"(w2));
        asm volatile("vfdotpex.s.h %0, %1, %2;" : "+&r"(sp) : "r"(s3), "r"(w3));
      }

      /* tail channels */
      for (; d < matrix_D; d += 2) {
        v2h sd = (v2h)0.0f;
        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            uint32_t kernel_base = ik * kernel_row_stride + jk * matrix_D;
            __fp16 *ptrW = (__fp16 *)0;
            __fp16 *ptrA = (__fp16 *)0;
            if (interior) {
              ptrW = &Wd[kernel_base + d];
              ptrA =
                  &A[interior_base + ik * image_row_stride + jk * matrix_D + d];
            } else {
              int32_t ia = ia_start + (int32_t)ik;
              int32_t ja = ja_start + (int32_t)jk;
              if ((ia >= 0) && (ja >= 0) && (ia < (int32_t)matrix_M) &&
                  (ja < (int32_t)matrix_N)) {
                ptrW = &Wd[kernel_base + d];
                ptrA = &A[(uint32_t)ia * image_row_stride +
                          (uint32_t)ja * matrix_D + d];
              }
            }
            if (ptrW && ptrA) {
              v2h w = *(v2h *)&(ptrW[0]);
              v2h a = *(v2h *)&(ptrA[0]);
              asm volatile("vfmac.h %0, %1, %2;" : "+r"(sd) : "r"(a), "r"(w));
            }
          }
        }
        v2h w = *(v2h *)&(Wp[k * matrix_D + d]);
        asm volatile("vfdotpex.s.h %0, %1, %2;" : "+&r"(sp) : "r"(sd), "r"(w));
      }

      asm volatile("fcvt.h.s %0, %1;" : "=r"(sum_f16) : "r"(sp));
      B[i * matrix_N * kernel_D + j * kernel_D + k] = sum_f16;
    }
  }
  return;
}
