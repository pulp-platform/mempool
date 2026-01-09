// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "baremetal/mempool_matmul_f16.h"
#include "builtins_v2.h"

/**
  @brief         Computes 1D convolution.
  @param[in]     Ci    dimension input channel
  @param[in]     Co    dimension output channel
  @param[in]     Wi    dimension convolution width
  @param[in]     Wf    dimension filter width
  @param[in]     X     input matrix  size: loop * Cin * Win
  @param[in]     F     filter matrix size: Cout * Cin * Wf
  @param[in]     b     bias vector   size: Cout
  @param[out]    Y     output matrix size: loop * Cout * Win
  @return        none
*/

void conv1d_f16(__fp16 const *__restrict__ X, __fp16 const *__restrict__ F,
                __fp16 const *__restrict__ b, __fp16 *__restrict__ Y,
                uint32_t Ci, uint32_t Co, uint32_t Wi, uint32_t Wf) {

  uint32_t pad = Wf / 2;

  for (uint32_t i = 0; i < Co; i++) {
    for (uint32_t j = 0; j < Wi; j++) {
      __fp16 sum = b[i];
      for (uint32_t k = 0; k < Ci; k++) {
        for (uint32_t f = 0; f < Wf; f++) {
          int32_t x_j = (int32_t)j - (int32_t)pad + (int32_t)f;
          if (x_j >= 0 && x_j < (int32_t)Wi) {
            uint32_t x_idx = k * Wi + (uint32_t)x_j;
            uint32_t f_idx = (i * Ci + k) * Wf + f;
            asm volatile("fmadd.h %[s], %[x], %[f], %[s];"
                         : [s] "+&r"(sum)
                         : [x] "r"(X[x_idx]), [f] "r"(F[f_idx]));
          }
        }
      }
      Y[i * Wi + j] = sum;
    }
  }

  return;
}

/**
  @brief         Computes 1D im2col transformation.
  @param[in]     Ci         dimension input channel
  @param[in]     Wi         dimension convolution width
  @param[in]     Wf         dimension filter width
  @param[in]     X          input matrix  size: Cin * Win
  @param[in]     X_im2col   output matrix  size: Cin * Win * Wf
  @return        none
*/

void im2col1d_f16(__fp16 const *__restrict__ X, __fp16 *__restrict__ X_im2col,
                  uint32_t Ci, uint32_t Wi, uint32_t Wf) {
  uint32_t pad = Wf / 2;
  for (uint32_t row = 0; row < Ci * Wf; row++) {
    uint32_t i = row / Wf;
    uint32_t f = row % Wf;
    for (uint32_t j = 0; j < Wi; j++) {
      int32_t xj = (int32_t)j - (int32_t)pad + (int32_t)f;
      if (xj >= 0 && xj < (int32_t)Wi) {
        X_im2col[row * Wi + j] = X[i * Wi + (uint32_t)xj];
      } else {
        X_im2col[row * Wi + j] = 0;
      }
    }
  }
  return;
}

/**
  @brief         Computes 1D convolution.
  @param[in]     Ci    dimension input channel
  @param[in]     Co    dimension output channel
  @param[in]     Wi    dimension convolution width
  @param[in]     Wf    dimension filter width
  @param[in]     X     input matrix  size: loop * Cin * Win
  @param[in]     F     filter matrix size: Cout * Cin * Wf
  @param[in]     b     bias vector   size: Cout
  @param[out]    Y     output matrix size: loop * Cout * Win
  @return        none
*/

void conv1d_im2col_matmul_f16(
    const __fp16 *__restrict__ X,  // [Ci][Wi]
    const __fp16 *__restrict__ F,  // [Co][Ci*Wf]
    const __fp16 *__restrict__ b,  // [Co]
    __fp16 *__restrict__ X_im2col, // [Ci*Wf][Wi] scratch
    __fp16 *__restrict__ Y,        // [Co][Wi]
    uint32_t Ci, uint32_t Co, uint32_t Wi, uint32_t Wf) {
  // Transformation
  im2col1d_f16(X, X_im2col, Ci, Wi, Wf);
  // GEMM
  matmul_2x2_single_f16(F, X_im2col, Y, Co, Ci * Wf, Wi);
  for (uint32_t i = 0; i < Co; i++) {
    for (uint32_t j = 0; j < Wi; j++) {
      asm volatile("fadd.h %[y], %[y], %[b];"
                   : [y] "+&r"(Y[i * Wi + j])
                   : [b] "r"(b[i]));
    }
  }
  return;
}
