// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

/**
  @brief         Single-core solution of lower triangular system
  @param[in]     pL input triangular matrix
  @param[in]     y known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @return        none
*/

void mempool_Ltrisol_q16vecs(int16_t *pL, int16_t *y, int16_t *x,
                             const uint32_t n) {

  uint32_t i, j;
  int32_t as, bs, diag;
  v2s ab, cd;
  v2s res = (v2s){0, 0};
  v2s ndc = (v2s){0, 0};

  // Solve for each variable x[i] in loop
  for (i = 0; i < n; i++) {
    // Pre-load the diagonal element
    diag = pL[2U * (i * n + i)];
    // Initialize the sums
    as = 0;
    bs = 0;
    // Use the previously solved variables to compute the sum
    for (j = 0; j < i; j++) {
      ab = *(v2s *)&pL[2U * (i * n + j)];
      cd = *(v2s *)&x[2U * j];
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
    as = as - (int32_t)y[2U * i];
    bs = bs - (int32_t)y[2U * i + 1];
    asm volatile("div       %[as], %[as], %[diag];"
                 "div       %[bs], %[bs], %[diag];"
                 "pv.pack   %[res], %[as], %[bs];"
                 : [as] "+&r"(as), [bs] "+&r"(bs), [res] "+&r"(res)
                 : [diag] "r"(diag)
                 :);
    (*(v2s *)&x[2U * i]) = res;
  }

  return;
}

/**
  @brief         Single-core solution of upper triangular system
                 (from transposed lower triangular system)
  @param[in]     pL input triangular matrix to be transposed
  @param[in]     y known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @return        none
*/

void mempool_Lttrisol_q16vecs(int16_t *pL, int16_t *y, int16_t *x,
                              const uint32_t n) {

  uint32_t i, j;
  int32_t as, bs, diag;
  v2s ab, cd;
  v2s res = (v2s){0, 0};
  v2s ndc = (v2s){0, 0};

  // Solve for each variable x[i] in loop
  for (i = 0; i < n; i++) {
    // Pre-load the diagonal element
    diag = pL[2 * ((n - 1 - i) * n + (n - 1 - i))];
    // Initialize the sums
    as = 0;
    bs = 0;
    // Use the previously solved variables to compute the sum
    for (j = 0; j < i; j++) {
      ab = *(v2s *)&pL[2U * ((n - 1 - j) * n + (n - 1 - i))];
      cd = *(v2s *)&x[2U * (n - 1 - j)];
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
    as = as - (int32_t)y[2 * (n - i - 1)];
    bs = bs - (int32_t)y[2 * (n - i - 1) + 1];
    asm volatile("div       %[as], %[as], %[diag];"
                 "div       %[bs], %[bs], %[diag];"
                 "pv.pack   %[res], %[as], %[bs];"
                 : [as] "+&r"(as), [bs] "+&r"(bs), [res] "+&r"(res)
                 : [diag] "r"(diag)
                 :);
    (*(v2s *)&x[2U * (n - i - 1)]) = res;
  }

  return;
}
