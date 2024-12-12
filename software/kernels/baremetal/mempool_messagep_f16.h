// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

void fullyconn_f16s(__fp16 const *__restrict__ A, __fp16 *B,
                    __fp16 *__restrict__ W, uint32_t M, uint32_t N,
                    uint32_t bias, uint32_t relu) {

  uint32_t i, j;
  v2h a, w;
  __fp16 b_f16;
  float b;

  for (i = 0; i < M; i++) {
    // Initialize accumulator
    if (bias) {
      b_f16 = B[i];
      asm volatile("fcvt.h.s %0, %1;" : "+r"(b) : "r"(b_f16));
    } else {
      b = 0.0f;
    }
    // Matrix vector multiply
    for (j = 0; j < N; j += 2) {
      a = *(v2h *)&A[j];
      w = *(v2h *)&W[i * N + j];
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

void fullyconn_f16s_unrolled4(__fp16 const *__restrict__ A, __fp16 *B,
                              __fp16 *__restrict__ W, uint32_t M, uint32_t N,
                              uint32_t bias, uint32_t relu) {

  uint32_t i, j;
  v2h w0, w1, w2, w3;
  v2h a0, a1, a2, a3;
  __fp16 b_f16;
  float b;

  for (i = 0; i < M; i++) {
    // Initialize accumulator
    if (bias) {
      b_f16 = B[i];
      asm volatile("fcvt.h.s %0, %1;" : "+r"(b) : "r"(b_f16));
    } else {
      b = 0.0f;
    }
    // Matrix vector multiply
    for (j = 0; j < N; j += 2) {
      a0 = *(v2h *)&A[j + 0];
      a1 = *(v2h *)&A[j + 2];
      a2 = *(v2h *)&A[j + 4];
      a3 = *(v2h *)&A[j + 6];
      w0 = *(v2h *)&W[i * N + j + 0];
      w1 = *(v2h *)&W[i * N + j + 2];
      w2 = *(v2h *)&W[i * N + j + 4];
      w3 = *(v2h *)&W[i * N + j + 6];
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
