// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "builtins_v2.h"
#include "hal_redmule.h"

void conv2d_pointwise_f16(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                          uint32_t matrix_N, uint32_t matrix_D,
                          uint32_t kernel_D, uint32_t core_id,
                          uint32_t numThreads) {

#if NUM_REDMULE_TILES > 0
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  if (redmule_id < num_redmules) {
    uint16_t M = (uint16_t)(matrix_M * matrix_N) / num_redmules;
    uint16_t N = (uint16_t)matrix_D;
    uint16_t P = (uint16_t)kernel_D;
    unsigned int I_ptr =
        (unsigned int)(A + redmule_id * (M * N / num_redmules));
    unsigned int O_ptr =
        (unsigned int)(B + redmule_id * (M * P / num_redmules));
    unsigned int W_ptr = (unsigned int)(W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, GEMM, Float16);
    mempool_wait(10);
    hwpe_trigger_job();
    mempool_wfi();
  }
  mempool_barrier(numThreads);
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
  if (numThreads > 1) {
    mempool_barrier(numThreads);
  }
#endif
  return;
}

void conv2d_depthwise_f16(__fp16 *A, __fp16 *B, __fp16 *W, uint32_t matrix_M,
                          uint32_t matrix_N, uint32_t matrix_D,
                          uint32_t kernel_K, uint32_t core_id,
                          uint32_t numThreads) {

  uint32_t i, j, k, d;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  for (k = core_id; k < matrix_M * matrix_N; k += numThreads) {
    i = k / matrix_N;
    j = k % matrix_N;

    /* unrolled chunks of 8 channels */
    for (d = 0; d + 8 <= matrix_D; d += 8) {
      v2h s0 = (v2h)0.0f, s1 = (v2h)0.0f, s2 = (v2h)0.0f, s3 = (v2h)0.0f;
      for (ik = 0; ik < kernel_K; ik++) {
        for (jk = 0; jk < kernel_K; jk++) {
          ia = (i - pad) + ik;
          ja = (j - pad) + jk;
          if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
            __fp16 *ptrW = W + ik * kernel_K * matrix_D + jk * matrix_D;
            __fp16 *ptrA = A + ia * matrix_N * matrix_D + ja * matrix_D;
            v2h w0 = *(v2h *)&(ptrW[d]);
            v2h w1 = *(v2h *)&(ptrW[d + 2]);
            v2h w2 = *(v2h *)&(ptrW[d + 4]);
            v2h w3 = *(v2h *)&(ptrW[d + 6]);
            v2h a0 = *(v2h *)&(ptrA[d]);
            v2h a1 = *(v2h *)&(ptrA[d + 2]);
            v2h a2 = *(v2h *)&(ptrA[d + 4]);
            v2h a3 = *(v2h *)&(ptrA[d + 6]);
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

    /* remaining channels */
    for (; d < matrix_D; d += 2) {
      v2h sum = (v2h)0.0f;
      for (ik = 0; ik < kernel_K; ik++) {
        for (jk = 0; jk < kernel_K; jk++) {
          ia = (i - pad) + ik;
          ja = (j - pad) + jk;
          if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
            v2h w = *(v2h *)&(W[ik * kernel_K * matrix_D + jk * matrix_D + d]);
            v2h a = *(v2h *)&(A[ia * matrix_N * matrix_D + ja * matrix_D + d]);
            asm volatile("vfmac.h %0, %1, %2;" : "+r"(sum) : "r"(a), "r"(w));
          }
        }
      }
      *((v2h *)&B[i * matrix_N * matrix_D + j * matrix_D + d]) = sum;
    }
  }

  if (numThreads > 1) {
    mempool_barrier(numThreads);
  }
  return;
}

void conv2d_depthwise_pointwise_f16(__fp16 *A, __fp16 *B, __fp16 *Wd,
                                    __fp16 *Wp, uint32_t matrix_M,
                                    uint32_t matrix_N, uint32_t matrix_D,
                                    uint32_t kernel_K, uint32_t kernel_D,
                                    uint32_t core_id, uint32_t numThreads) {

  uint32_t l, i, j, d, k;
  uint32_t ik, jk, ia, ja;
  uint32_t pad = kernel_K / 2;

  __fp16 sum_f16;
  float sp;

  for (l = core_id; l < matrix_M * matrix_N; l += numThreads) {
    i = l / matrix_N;
    j = l % matrix_N;

    for (k = 0; k < kernel_D; k++) {
      sp = 0.0f;

      /* unrolled 8-channel chunks */
      for (d = 0; d + 8 <= matrix_D; d += 8) {
        v2h s0 = (v2h)0.0f, s1 = (v2h)0.0f, s2 = (v2h)0.0f, s3 = (v2h)0.0f;
        for (ik = 0; ik < kernel_K; ik++) {
          for (jk = 0; jk < kernel_K; jk++) {
            ia = (i - pad) + ik;
            ja = (j - pad) + jk;
            if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
              __fp16 *ptrW = &Wd[ik * kernel_K * matrix_D + jk * matrix_D];
              __fp16 *ptrA = &A[ia * matrix_N * matrix_D + ja * matrix_D];
              v2h w0 = *(v2h *)&(ptrW[d]);
              v2h w1 = *(v2h *)&(ptrW[d + 2]);
              v2h w2 = *(v2h *)&(ptrW[d + 4]);
              v2h w3 = *(v2h *)&(ptrW[d + 6]);
              v2h a0 = *(v2h *)&(ptrA[d]);
              v2h a1 = *(v2h *)&(ptrA[d + 2]);
              v2h a2 = *(v2h *)&(ptrA[d + 4]);
              v2h a3 = *(v2h *)&(ptrA[d + 6]);
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
            ia = (i - pad) + ik;
            ja = (j - pad) + jk;
            if ((ia >= 0) && (ja >= 0) && (ia < matrix_M) && (ja < matrix_N)) {
              v2h w =
                  *(v2h *)&(Wd[ik * kernel_K * matrix_D + jk * matrix_D + d]);
              v2h a =
                  *(v2h *)&(A[ia * matrix_N * matrix_D + ja * matrix_D + d]);
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

  if (numThreads > 1) {
    mempool_barrier(numThreads);
  }

  return;
}
