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
  @param[in]     folded matrix L is folded row-wise in memory
  @return        none
*/

void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n,
                          const uint32_t transposed, const uint32_t folded) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ax, bx;
  __fp16 diag;
  const uint32_t offset = folded ? NUM_BANKS : n;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    uint32_t ridx = transposed ? (n - i - 1) : i;
    diag = pL[2U * (ridx * offset + ridx)];
    as = (__fp16)in[2U * ridx];
    bs = (__fp16)in[2U * ridx + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {

      uint32_t cidx = transposed ? (n - j - 1) : j;
      c = x[2U * cidx];
      d = x[2U * cidx + 1];
      if (transposed) {
        a = pL[2U * (cidx * offset + ridx)];
        b = pL[2U * (cidx * offset + ridx) + 1];
        asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                     "fnmsub.h  %[as], %[b], %[d], %[as];"
                     "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                     "fmadd.h   %[bs], %[b], %[c], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      } else {
        a = pL[2U * (ridx * offset + cidx)];
        b = pL[2U * (ridx * offset + cidx) + 1];
        asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                     "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                     "fmadd.h   %[as], %[b], %[d], %[as];"
                     "fnmsub.h  %[bs], %[b], %[c], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.h %[ax], %[as], %[diag];"
                 "fdiv.h %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * ridx] = ax;
    x[2U * ridx + 1] = bx;
  }
  return;
}

#else

/**
  @brief         Single-core solution of lower triangular system
  @param[in]     pL input triangular matrix
  @param[in]     in known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @return        none
*/

void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n,
                          const uint32_t transposed, const uint32_t folded) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 diag;
  const uint32_t offset = folded ? NUM_BANKS : n;

  float ax, bx, diag_f32;
  v2h res;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    uint32_t ridx = transposed ? (n - i - 1) : i;
    diag = pL[2U * (ridx * offset + ridx)];
    as = (__fp16)in[2U * ridx];
    bs = (__fp16)in[2U * ridx + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {

      uint32_t volatile cidx = transposed ? (n - j - 1) : j;
      c = x[2U * cidx];
      d = x[2U * cidx + 1];
      if (transposed) {
        a = pL[2U * (cidx * offset + ridx)];
        b = pL[2U * (cidx * offset + ridx) + 1];
        asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                     "fnmsub.h  %[as], %[b], %[d], %[as];"
                     "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                     "fmadd.h   %[bs], %[b], %[c], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      } else {
        a = pL[2U * (ridx * offset + cidx)];
        b = pL[2U * (ridx * offset + cidx) + 1];
        asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                     "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                     "fmadd.h   %[as], %[b], %[d], %[as];"
                     "fnmsub.h  %[bs], %[b], %[c], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fcvt.s.h %0, %1;" : "=r"(diag_f32) : "r"(diag) :);
    asm volatile("fcvt.s.h %0, %1;" : "=r"(ax) : "r"(as) :);
    asm volatile("fcvt.s.h %0, %1;" : "=r"(bx) : "r"(bs) :);
    ax = ax / diag_f32;
    bx = bx / diag_f32;
    asm volatile("vfcpka.h.s %0, %1, %2;" : "=r"(res) : "r"(ax), "r"(bx) :);
    (*(v2h *)&x[2U * ridx]) = res;
  }
  return;
}

#endif
