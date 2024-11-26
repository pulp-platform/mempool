// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

/**
  @brief         Single-core solution of lower triangular system
  @param[in]     pL input triangular matrix
  @param[in]     y known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @param[in]     transposed solve transposed system
  @return        none
*/

void mempool_Ltrisol_q16vecs(int16_t *pL, int16_t *y, int16_t *x,
                             const uint32_t n, const uint32_t transposed) {

  uint32_t i, j;
  int32_t as, bs, diag;
  v2s ab, cd;
  v2s res = (v2s){0, 0};
  v2s ndc = (v2s){0, 0};

  // Solve for each variable x[i] in loop
  for (i = 0; i < n; i++) {
    uint32_t ridx = transposed ? (n - i - 1) : i;
    diag = pL[2U * (ridx + ridx)];
    // Initialize the sums
    as = 0;
    bs = 0;
    // Use the previously solved variables to compute the sum
    for (j = 0; j < i; j++) {
      uint32_t cidx = transposed ? (n - j - 1) : j;
      if (!transposed) {
        ab = *(v2s *)&pL[2U * (ridx * n + cidx)];
      } else {
        ab = *(v2s *)&pL[2U * (cidx * n + ridx)];
      }
      cd = *(v2s *)&x[2U * cidx];
      const uint32_t shuffle_mask = 0x00020003;
      asm volatile(
          // s = s + (ac + bd) + j(bc - ad)
          "pv.dotsp.h     %[as],  %[ab],   %[cd];"
          "pv.shuffle2.h  %[ndc], %[cd],   %[shuffle_mask];"
          "pv.sub.h       %[ndc], %[zero], %[ndc];"
          "pv.dotsp.h     %[bs],  %[ab],   %[ndc];"
          "srai           %[as],  %[as],   0x8;"
          "srai           %[bs],  %[bs],   0x8;"
          "p.clip         %[bs],  %[bs],   0x16;"
          "p.clip         %[as],  %[as],   0x16;"
          : [as] "+&r"(as), [bs] "+&r"(bs), [ndc] "+r"(ndc)
          : [ab] "r"(ab), [cd] "r"(cd), [shuffle_mask] "r"(shuffle_mask),
            [zero] "r"((v2s){0, 0})
          :);
    }
    // Subtract the sum from y[i] and divide by the diagonal element L[i][i]
    as = as - (int32_t)y[2U * ridx];
    bs = bs - (int32_t)y[2U * ridx + 1];
    asm volatile("div       %[as], %[as], %[diag];"
                 "div       %[bs], %[bs], %[diag];"
                 "pv.pack   %[res], %[as], %[bs];"
                 : [as] "+&r"(as), [bs] "+&r"(bs), [res] "+&r"(res)
                 : [diag] "r"(diag)
                 :);
    (*(v2s *)&x[2U * ridx]) = res;
  }

  return;
}
