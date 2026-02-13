// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "builtins_v2.h"
#include "hal_redmule.h"

void fullyconn_4x2_parallel_f16(const __fp16 *__restrict__ pSrcA,
                                const __fp16 *__restrict__ pSrcB,
                                __fp16 *__restrict__ pDstC, uint32_t M,
                                uint32_t N, uint32_t P, uint32_t bias,
                                uint32_t relu, uint32_t core_id,
                                uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  for (i = core_id * 4; i < M; i += numThreads * 4) {
    for (k = 0; k < P; k += 2) {

      __fp16 c00, c01, c10, c11;
      __fp16 c20, c21, c30, c31;

      if (bias) {
        c00 = pDstC[(i + 0) * P + (k + 0)];
        c01 = pDstC[(i + 0) * P + (k + 1)];
        c10 = pDstC[(i + 1) * P + (k + 0)];
        c11 = pDstC[(i + 1) * P + (k + 1)];
        c20 = pDstC[(i + 2) * P + (k + 0)];
        c21 = pDstC[(i + 2) * P + (k + 1)];
        c30 = pDstC[(i + 3) * P + (k + 0)];
        c31 = pDstC[(i + 3) * P + (k + 1)];
      } else {
        c00 = c01 = c10 = c11 = c20 = c21 = c30 = c31 = (__fp16)0.0f;
      }

      for (j = 0; j < N; j += 2) {
        __fp16 a00 = pSrcA[i * N + j];
        __fp16 a01 = pSrcA[i * N + j + 1];
        __fp16 a10 = pSrcA[(i + 1) * N + j];
        __fp16 a11 = pSrcA[(i + 1) * N + j + 1];
        __fp16 a20 = pSrcA[(i + 2) * N + j];
        __fp16 a21 = pSrcA[(i + 2) * N + j + 1];
        __fp16 a30 = pSrcA[(i + 3) * N + j];
        __fp16 a31 = pSrcA[(i + 3) * N + j + 1];
        __fp16 b00 = pSrcB[j * P + k];
        __fp16 b01 = pSrcB[j * P + k + 1];
        __fp16 b10 = pSrcB[(j + 1) * P + k];
        __fp16 b11 = pSrcB[(j + 1) * P + k + 1];
        asm volatile(
            "fmadd.h %[c00], %[a00], %[b00], %[c00];"
            "fmadd.h %[c00], %[a01], %[b10], %[c00];"
            "fmadd.h %[c01], %[a00], %[b01], %[c01];"
            "fmadd.h %[c01], %[a01], %[b11], %[c01];"
            "fmadd.h %[c10], %[a10], %[b00], %[c10];"
            "fmadd.h %[c10], %[a11], %[b10], %[c10];"
            "fmadd.h %[c11], %[a10], %[b01], %[c11];"
            "fmadd.h %[c11], %[a11], %[b11], %[c11];"
            "fmadd.h %[c20], %[a20], %[b00], %[c20];"
            "fmadd.h %[c20], %[a21], %[b10], %[c20];"
            "fmadd.h %[c21], %[a20], %[b01], %[c21];"
            "fmadd.h %[c21], %[a21], %[b11], %[c21];"
            "fmadd.h %[c30], %[a30], %[b00], %[c30];"
            "fmadd.h %[c30], %[a31], %[b10], %[c30];"
            "fmadd.h %[c31], %[a30], %[b01], %[c31];"
            "fmadd.h %[c31], %[a31], %[b11], %[c31];"
            : [c00] "+&r"(c00), [c01] "+&r"(c01), [c10] "+&r"(c10),
              [c11] "+&r"(c11), [c20] "+&r"(c20), [c21] "+&r"(c21),
              [c30] "+&r"(c30), [c31] "+&r"(c31)
            : [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10), [b11] "r"(b11),
              [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),
              [a20] "r"(a20), [a21] "r"(a21), [a30] "r"(a30), [a31] "r"(a31)
            :);
      }

      // ReLU
      if (relu) {
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c00) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c01) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c10) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c11) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c20) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c21) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c30) : :);
        asm volatile("fmax.h %0, %0, zero;" : "+r"(c31) : :);
      }
      // Store
      pDstC[i * P + k] = c00;
      pDstC[i * P + k + 1] = c01;
      pDstC[(i + 1) * P + k] = c10;
      pDstC[(i + 1) * P + k + 1] = c11;
      pDstC[(i + 2) * P + k] = c20;
      pDstC[(i + 2) * P + k + 1] = c21;
      pDstC[(i + 3) * P + k] = c30;
      pDstC[(i + 3) * P + k + 1] = c31;
    }
  }
}

/*
  The kernel combines the information from P tensors by averaging over
  the P dimension

  P: message passing instances of the tensor
  M: rows of the input tensor (as in 2D matrix)
  N: columns of the input tensor (as in 2D matrix)
  D: depth of the input tensor

  Parameters of optional hiddel layer:

  HL:    pointer to hiddel layer output
  W_fc1: weights of first fully-connected layer
  W_fc2: weights of second fully-connected layer
  Dhl:   depth of the hidden-layer
  bias:  optional bias
  relu:  optional relu
*/
void messagep_f16(__fp16 *A, __fp16 *B, __fp16 __attribute__((unused)) * HL,
                  __fp16 __attribute__((unused)) * W_fc1,
                  __fp16 __attribute__((unused)) * W_fc2, uint32_t P,
                  uint32_t M, uint32_t N, uint32_t D,
                  uint32_t __attribute__((unused)) Dhl, uint32_t fc_layer,
                  uint32_t __attribute__((unused)) bias,
                  uint32_t __attribute__((unused)) relu, uint32_t core_id,
                  uint32_t numThreads) {

  uint32_t p, i;

  __fp16 P_f16;
  asm volatile("fcvt.h.wu %0, %1" : "+r"(P_f16) : "r"(P));
  asm volatile("pv.pack %0, %0, %0" : "+r"(P_f16));

  // Apply FC-layer
  if (fc_layer) {
#if NUM_REDMULE_TILES > 0
    uint32_t redmule_id = mempool_get_redmule_id();
    uint32_t num_redmules = mempool_get_redmule_count();
    // Loops over the message passing instances
    for (p = redmule_id; p < P; p += num_redmules) {
      if (redmule_id < num_redmules) {
        // Layer 1
        uint16_t dim_M = (uint16_t)(M * N);
        uint16_t dim_N = (uint16_t)D;
        uint16_t dim_P = (uint16_t)Dhl;
        unsigned int I_ptr = (unsigned int)(A + p * M * N * D);
        unsigned int O_ptr = (unsigned int)(HL + p * M * N * Dhl);
        unsigned int W_ptr = (unsigned int)(W_fc1 + p * Dhl * D);
        hwpe_soft_clear();
        mempool_wait(10);
        redmule_cfg(I_ptr, W_ptr, O_ptr, dim_M, dim_N, dim_P, 0, GEMM, Float16);
        mempool_wait(10);
        hwpe_trigger_job();
        mempool_wfi();
        // Layer 2
        dim_M = (uint16_t)(M * N);
        dim_N = (uint16_t)Dhl;
        dim_P = (uint16_t)D;
        I_ptr = (unsigned int)(HL + p * M * N * Dhl);
        O_ptr = (unsigned int)(A + p * M * N * D);
        W_ptr = (unsigned int)(W_fc2 + p * Dhl * D);
        hwpe_soft_clear();
        mempool_wait(10);
        redmule_cfg(I_ptr, W_ptr, O_ptr, dim_M, dim_N, dim_P, 0, GEMM, Float16);
        mempool_wait(10);
        hwpe_trigger_job();
        mempool_wfi();
      }
    }
#else
    uint32_t numThreads_P = numThreads > 1 ? numThreads / P : 1;
    uint32_t core_id_P = core_id % numThreads_P;
    // Loops over the message passing instances
    for (p = 0; p < P; p++) {
      // Compute the dense layer (Dhl == depth of the hidden layer)
      __fp16 *ptrA = &A[p * M * N * D];
      __fp16 *ptrHL = &HL[p * M * N * Dhl];
      __fp16 *ptrW1 = &W_fc1[p * D * Dhl];
      __fp16 *ptrW2 = &W_fc2[p * D * Dhl];
      fullyconn_4x2_parallel_f16(ptrA, ptrW1, ptrHL, M * N, D, Dhl, bias, relu,
                                 core_id_P, numThreads_P);
      fullyconn_4x2_parallel_f16(ptrHL, ptrW2, ptrA, M * N, Dhl, D, bias, 0,
                                 core_id_P, numThreads_P);
    }
#endif
  }
  if (numThreads > 1) {
    mempool_barrier(numThreads);
  }

  v2h a0, a1, a2, a3;
  // Loops over the 3D image
  for (i = 2 * core_id; i < M * N * D; i += 2 * numThreads) {
    v2h sum0 = (v2h)0.0f;
    v2h sum1 = (v2h)0.0f;
    v2h sum2 = (v2h)0.0f;
    v2h sum3 = (v2h)0.0f;
    // Sum over all p's
    for (p = 0; p < P; p += 4) {
      a0 = *(v2h *)&A[(p + 0) * M * N * D + i];
      a1 = *(v2h *)&A[(p + 1) * M * N * D + i];
      a2 = *(v2h *)&A[(p + 2) * M * N * D + i];
      a3 = *(v2h *)&A[(p + 3) * M * N * D + i];
      asm volatile("vfadd.h %0, %0, %1" : "+r"(sum0) : "r"(a0));
      asm volatile("vfadd.h %0, %0, %1" : "+r"(sum1) : "r"(a1));
      asm volatile("vfadd.h %0, %0, %1" : "+r"(sum2) : "r"(a2));
      asm volatile("vfadd.h %0, %0, %1" : "+r"(sum3) : "r"(a3));
    }
    v2h res = sum0;
    asm volatile("vfadd.h %0, %0, %1" : "+r"(res) : "r"(sum1));
    asm volatile("vfadd.h %0, %0, %1" : "+r"(res) : "r"(sum2));
    asm volatile("vfadd.h %0, %0, %1" : "+r"(res) : "r"(sum3));
    // Subtract one p
    for (p = 0; p < P; p += 4) {
      sum0 = res;
      sum1 = res;
      sum2 = res;
      sum3 = res;
      a0 = *(v2h *)&A[(p + 0) * M * N * D + i];
      a1 = *(v2h *)&A[(p + 1) * M * N * D + i];
      a2 = *(v2h *)&A[(p + 2) * M * N * D + i];
      a3 = *(v2h *)&A[(p + 3) * M * N * D + i];
      asm volatile("vfsub.h %0, %0, %1" : "+r"(sum0) : "r"(a0));
      asm volatile("vfsub.h %0, %0, %1" : "+r"(sum1) : "r"(a0));
      asm volatile("vfsub.h %0, %0, %1" : "+r"(sum2) : "r"(a0));
      asm volatile("vfsub.h %0, %0, %1" : "+r"(sum3) : "r"(a0));
      asm volatile("vfdiv.h %0, %0, %1" : "+r"(sum0) : "r"(P_f16));
      asm volatile("vfdiv.h %0, %0, %1" : "+r"(sum1) : "r"(P_f16));
      asm volatile("vfdiv.h %0, %0, %1" : "+r"(sum2) : "r"(P_f16));
      asm volatile("vfdiv.h %0, %0, %1" : "+r"(sum3) : "r"(P_f16));
      *((v2h *)&B[(p + 0) * M * N * D + i]) = sum0;
      *((v2h *)&B[(p + 1) * M * N * D + i]) = sum1;
      *((v2h *)&B[(p + 2) * M * N * D + i]) = sum2;
      *((v2h *)&B[(p + 3) * M * N * D + i]) = sum3;
    }
  }
  if (numThreads > 1) {
    mempool_barrier(numThreads);
  }

  return;
}
