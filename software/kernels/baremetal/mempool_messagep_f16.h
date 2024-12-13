// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

static inline void fullyconn_f16s(__fp16 const *__restrict__ A, __fp16 *B,
                                  __fp16 *__restrict__ W, uint32_t wM,
                                  uint32_t wN, uint32_t bias, uint32_t relu) {

  uint32_t i, j;
  v2h a, w;
  __fp16 b_f16;
  float b;

  for (i = 0; i < wM; i++) {
    // Initialize accumulator
    if (bias) {
      b_f16 = B[i];
      asm volatile("fcvt.h.s %0, %1;" : "+r"(b) : "r"(b_f16));
    } else {
      b = 0.0f;
    }
    // Matrix vector multiply
    for (j = 0; j < wN; j += 2) {
      a = *(v2h *)&A[j];
      w = *(v2h *)&W[i * wN + j];
      asm volatile("vfdotpex.s.h %0, %1, %2;" : "+r"(b) : "r"(a), "r"(w));
    }
    // ReLU
    b = (b < 0.0f) && (relu == 1) ? 0.0f : b;
    // Store output
    asm volatile("fcvt.h.s %0, %1;" : "+r"(b_f16) : "r"(b));
    B[i] = b_f16;
  }

  return;
}

static inline void fullyconn_f16s_unrolled4(__fp16 const *__restrict__ A,
                                            __fp16 *B, __fp16 *__restrict__ W,
                                            uint32_t wM, uint32_t wN,
                                            uint32_t bias, uint32_t relu) {

  uint32_t i, j;
  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;
  __fp16 b_f16;
  float b;

  for (i = 0; i < wM; i++) {
    // Initialize accumulator
    if (bias) {
      b_f16 = B[i];
      asm volatile("fcvt.h.s %0, %1;" : "+r"(b) : "r"(b_f16));
    } else {
      b = 0.0f;
    }
    // Matrix vector multiply
    for (j = 0; j < wN; j += 2) {
      a0 = *(v2h *)&A[j + 0];
      a1 = *(v2h *)&A[j + 2];
      a2 = *(v2h *)&A[j + 4];
      a3 = *(v2h *)&A[j + 6];
      w0 = *(v2h *)&W[i * wN + j + 0];
      w1 = *(v2h *)&W[i * wN + j + 2];
      w2 = *(v2h *)&W[i * wN + j + 4];
      w3 = *(v2h *)&W[i * wN + j + 6];
      asm volatile("vfdotpex.s.h %0, %1, %2;" : "+r"(b) : "r"(a0), "r"(w0));
      asm volatile("vfdotpex.s.h %0, %1, %2;" : "+r"(b) : "r"(a1), "r"(w1));
      asm volatile("vfdotpex.s.h %0, %1, %2;" : "+r"(b) : "r"(a2), "r"(w2));
      asm volatile("vfdotpex.s.h %0, %1, %2;" : "+r"(b) : "r"(a3), "r"(w3));
    }
    // ReLU
    b = (b < 0.0f) && (relu == 1) ? 0.0f : b;
    // Store output
    asm volatile("fcvt.h.s %0, %1;" : "+r"(b_f16) : "r"(b));
    B[i] = b_f16;
  }

  return;
}

/*
  The kernel combines the information from matrix_P tensors by averaging over
  the matrix_P dimension matrix_P: message passing instances of the tensor
  matrix_M: rows of the input tensor (as in 2D matrix)
  matrix_N: rows of the input tensor (as in 2D matrix)
  matrix_D: depth of the input tensor

  Parameters of optional hiddel layer:
  HL: pointer to hiddel layer output
  W_fc1: weights of first fully-connected layer
  W_fc2: weights of second fully-connected layer
  wHL: depth of the hidden-layer
  bias: optional bias
  relu: optional relu
*/
void messagep_f16s(__fp16 *A, __fp16 *B, uint32_t matrix_P, uint32_t matrix_M,
                   uint32_t matrix_N, uint32_t matrix_D, uint32_t fc_layer,
                   __fp16 __attribute__((unused)) * HL,
                   __fp16 __attribute__((unused)) * W_fc1,
                   __fp16 __attribute__((unused)) * W_fc2,
                   uint32_t __attribute__((unused)) wHL,
                   uint32_t __attribute__((unused)) bias,
                   uint32_t __attribute__((unused)) relu) {

  uint32_t p, i, j, d, mp;
  v2h a;
  v2h sum;

  __fp16 N_f16;
  asm volatile("fcvt.h.wu %0, %1" : "+r"(N_f16) : "r"(matrix_P));
  asm volatile("pv.pack %0, %0, %0" : "+r"(N_f16));

  // Loops over the 2D image
  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      // Apply FC-layer
      if (fc_layer) {
        // Loops over the message passing instances
        for (p = 0; p < matrix_P; p++) {
          // Compute the dense layer (wHL == depth of the hidden layer)
          __fp16 *ptr1 = &A[p * matrix_M * matrix_N * matrix_D +
                            i * matrix_N * matrix_D + j * matrix_D];
          __fp16 *ptr2 = &HL[p * matrix_M * matrix_N * matrix_D +
                             i * matrix_N * wHL + j * wHL];
          fullyconn_f16s(ptr1, ptr2, &W_fc1[p * wHL * matrix_D], wHL, matrix_D,
                         bias, relu);
          fullyconn_f16s(ptr2, ptr1, &W_fc2[p * matrix_D * wHL], matrix_D, wHL,
                         bias, relu);
        }
      }

      // Loops over the message passing instances
      for (p = 0; p < matrix_P; p++) {
        // Loop over depth and sum the message passing instances
        for (d = 0; d < matrix_D; d += 2) {
          sum = (v2h)0.0f;
          for (mp = p + 1; mp < matrix_P; mp++) {
            a = *(v2h *)&A[mp * matrix_M * matrix_N * matrix_D +
                           i * matrix_N * matrix_D + j * matrix_D + d];
            asm volatile("vfadd.h %0, %0, %1" : "+r"(sum) : "r"(a));
          }
          for (mp = 0; mp < p; mp++) {
            a = *(v2h *)&A[mp * matrix_M * matrix_N * matrix_D +
                           i * matrix_N * matrix_D + j * matrix_D + d];
            asm volatile("vfadd.h %0, %0, %1" : "+r"(sum) : "r"(a));
          }
          // Divide sum
          asm volatile("vfdiv.h %0, %0, %1" : "+r"(sum) : "r"(N_f16));
          *((v2h *)&B[p * matrix_M * matrix_N * matrix_D +
                      i * matrix_N * matrix_D + j * matrix_D + d]) = sum;
        }
      }
    }
  }

  return;
}

void messagep_f16s_unrolled4(__fp16 *A, __fp16 *B, uint32_t matrix_P,
                             uint32_t matrix_M, uint32_t matrix_N,
                             uint32_t matrix_D, uint32_t fc_layer,
                             __fp16 __attribute__((unused)) * HL,
                             __fp16 __attribute__((unused)) * W_fc1,
                             __fp16 __attribute__((unused)) * W_fc2,
                             uint32_t __attribute__((unused)) wHL,
                             uint32_t __attribute__((unused)) bias,
                             uint32_t __attribute__((unused)) relu) {

  uint32_t p, i, j, d, mp;
  v2h a0, a1, a2, a3;
  v2h s0, s1, s2, s3;

  __fp16 N_f16;
  asm volatile("fcvt.h.wu %0, %1" : "+r"(N_f16) : "r"(matrix_P));
  asm volatile("pv.pack %0, %0, %0" : "+r"(N_f16));

  // Loops over the 2D image
  for (i = 0; i < matrix_M; i++) {
    for (j = 0; j < matrix_N; j++) {

      // Apply FC-layer
      if (fc_layer) {
        // Loops over the message passing instances
        for (p = 0; p < matrix_P; p++) {
          // Compute the dense layer (wHL == depth of the hidden layer)
          __fp16 *ptr1 = &A[p * matrix_M * matrix_N * matrix_D +
                            i * matrix_N * matrix_D + j * matrix_D];
          __fp16 *ptr2 = &HL[p * matrix_M * matrix_N * matrix_D +
                             i * matrix_N * wHL + j * wHL];
          fullyconn_f16s_unrolled4(ptr1, ptr2, &W_fc1[p * wHL * matrix_D], wHL,
                                   matrix_D, bias, relu);
          fullyconn_f16s_unrolled4(ptr2, ptr1, &W_fc2[p * matrix_D * wHL],
                                   matrix_D, wHL, bias, relu);
        }
      }

      // Loops over the message passing instances
      for (p = 0; p < matrix_P; p++) {
        // Loop over depth and sum the message passing instances
        for (d = 0; d < matrix_D; d += 8) {
          s0 = (v2h)0.0f;
          s1 = (v2h)0.0f;
          s2 = (v2h)0.0f;
          s3 = (v2h)0.0f;
          for (mp = p + 1; mp < matrix_P; mp++) {
            __fp16 *a_ptr = &A[mp * matrix_M * matrix_N * matrix_D +
                               i * matrix_N * matrix_D + j * matrix_D];
            a0 = *(v2h *)&a_ptr[d];
            a1 = *(v2h *)&a_ptr[d + 2];
            a2 = *(v2h *)&a_ptr[d + 4];
            a3 = *(v2h *)&a_ptr[d + 6];
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s0) : "r"(a0));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s1) : "r"(a1));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s2) : "r"(a2));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s3) : "r"(a3));
          }
          for (mp = 0; mp < p; mp++) {
            __fp16 *a_ptr = &A[mp * matrix_M * matrix_N * matrix_D +
                               i * matrix_N * matrix_D + j * matrix_D];
            a0 = *(v2h *)&a_ptr[d];
            a1 = *(v2h *)&a_ptr[d + 2];
            a2 = *(v2h *)&a_ptr[d + 4];
            a3 = *(v2h *)&a_ptr[d + 6];
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s0) : "r"(a0));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s1) : "r"(a1));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s2) : "r"(a2));
            asm volatile("vfadd.h %0, %0, %1" : "+r"(s3) : "r"(a3));
          }
          // Divide sum
          asm volatile("vfdiv.h %0, %0, %1" : "+r"(s0) : "r"(N_f16));
          asm volatile("vfdiv.h %0, %0, %1" : "+r"(s1) : "r"(N_f16));
          asm volatile("vfdiv.h %0, %0, %1" : "+r"(s2) : "r"(N_f16));
          asm volatile("vfdiv.h %0, %0, %1" : "+r"(s3) : "r"(N_f16));
          __fp16 *b_ptr = &B[p * matrix_M * matrix_N * matrix_D +
                             i * matrix_N * matrix_D + j * matrix_D];
          *((v2h *)&b_ptr[d + 0]) = s0;
          *((v2h *)&b_ptr[d + 2]) = s1;
          *((v2h *)&b_ptr[d + 4]) = s2;
          *((v2h *)&b_ptr[d + 6]) = s3;
        }
      }
    }
  }

  return;
}
