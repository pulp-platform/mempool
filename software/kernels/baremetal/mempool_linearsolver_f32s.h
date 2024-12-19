// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#ifdef __XDIVSQRT

/**
  @brief         Single-core solution of lower triangular system
  @param[in]     pL input triangular matrix
  @param[in]     in known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @param[in]     transposed solve transposed system
  @return        none
*/

void mempool_Ltrisol_f32s(float *pL, float *in, float *x, const uint32_t n,
                          const uint32_t transposed, const uint32_t folded) {

  uint32_t i, j;
  float a, b;
  float c, d;

  float as, bs;
  float ax, bx;
  float diag;
  const uint32_t offset = folded ? NUM_BANKS : n;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    uint32_t ridx = transposed ? (n - i - 1) : i;
    diag = pL[2U * (ridx * offset + ridx)];
    as = in[2U * ridx];
    bs = in[2U * ridx + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {

      uint32_t cidx = transposed ? (n - j - 1) : j;
      if (!transposed) {
        a = pL[2U * (ridx * offset + cidx)];
        b = pL[2U * (ridx * offset + cidx) + 1];
      } else {
        a = pL[2U * (cidx * offset + ridx)];
        b = pL[2U * (cidx * offset + ridx) + 1];
      }

      c = x[2U * cidx];
      d = x[2U * cidx + 1];
      asm volatile("fnmsub.s %[as], %[a], %[c], %[as];"
                   "fnmsub.s %[bs], %[a], %[d], %[bs];"
                   "fmadd.s  %[as], %[b], %[d], %[as];"
                   "fnmsub.s %[bs], %[b], %[c], %[bs];"
                   : [as] "+&r"(as), [bs] "+&r"(bs)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                   :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.s %[ax], %[as], %[diag];"
                 "fdiv.s %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * ridx] = ax;
    x[2U * ridx + 1] = bx;
  }
  return;
}

#else

#error "ERROR: f32 MMSE functions available only for __XDIVSQRT."

#endif
