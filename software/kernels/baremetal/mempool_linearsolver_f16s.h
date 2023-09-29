// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

/**
  @brief         Single-core solution of lower triangular system
  @param[in]     pL input triangular matrix
  @param[in]     in known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @return        none
*/

void mempool_Ltrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x, const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    diag = pL[2 * (i * n + i)];
    as = (__fp16)in[2U * i];
    bs = (__fp16)in[2U * i + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * (i * n + j)];
      b = pL[2U * (i * n + j) + 1];
      c = x[2U * j];
      d = x[2U * j + 1];
      asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                   "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                   "fmadd.h   %[as], %[b], %[d], %[as];"
                   "fnmsub.h  %[bs], %[b], %[c], %[bs];"
                   : [as] "+&r"(as), [bs] "+&r"(bs)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                   :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.h %[ax], %[as], %[diag];"
                 "fdiv.h %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * i] = ax;
    x[2U * i + 1] = bx;
  }
  return;
}

/**
  @brief         Single-core solution of upper triangular system
                 (from transposed lower triangular system)
  @param[in]     pL input triangular matrix to be transposed
  @param[in]     in known variables vector
  @param[in]     x unknown solutions vector
  @param[in]     n dimension of the system
  @return        none
*/

void mempool_Lttrisol_f16s(__fp16 *pL, __fp16 *in, __fp16 *x,
                           const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    diag = pL[2 * ((n - 1 - i) * n + (n - 1 - i))];
    as = (__fp16)in[2 * (n - i - 1)];
    bs = (__fp16)in[2 * (n - i - 1) + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[2U * ((n - 1 - j) * n + (n - 1 - i))];
      b = pL[2U * ((n - 1 - j) * n + (n - 1 - i)) + 1];
      c = x[2U * (n - 1 - j)];
      d = x[2U * (n - 1 - j) + 1];
      asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                   "fnmsub.h  %[as], %[b], %[d], %[as];"
                   "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                   "fmadd.h   %[bs], %[b], %[c], %[bs];"
                   : [as] "+&r"(as), [bs] "+&r"(bs)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                   :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.h %[ax], %[as], %[diag];"
                 "fdiv.h %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * (n - i - 1)] = ax;
    x[2U * (n - i - 1) + 1] = bx;
  }
  return;
}

/**
  @brief        Single-core solution of lower triangular system
                (from transposed lower triangular system)
  @param[in]    pL input triangular matrix
  @param[in]    in known variables vector
  @param[in]    x unknown solutions vector
  @param[in]    n dimension of the system
  @return       none
*/

void mempool_Ltrisol_folded_f16s(__fp16 *pL, __fp16 *in, __fp16 *x,
                                 const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    diag = pL[i * N_BANKS + 2 * i];
    as = (__fp16)in[2U * i];
    bs = (__fp16)in[2U * i + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      a = pL[i * N_BANKS + 2 * j];
      b = pL[i * N_BANKS + 2 * j + 1];
      c = x[2U * j];
      d = x[2U * j + 1];
      asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                   "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                   "fmadd.h   %[as], %[b], %[d], %[as];"
                   "fnmsub.h  %[bs], %[b], %[c], %[bs];"
                   : [as] "+&r"(as), [bs] "+&r"(bs)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                   :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.h %[ax], %[as], %[diag];"
                 "fdiv.h %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * i] = ax;
    x[2U * i + 1] = bx;
  }
  return;
}

/**
  @brief        Single-core solution of upper triangular system
                Output data is folded to the core's local memory.
                (from transposed lower triangular system)
  @param[in]    pL input triangular matrix to be transposed
  @param[in]    in known variables vector
  @param[in]    x unknown solutions vector
  @param[in]    n dimension of the system
  @return       none
*/

void mempool_Lttrisol_folded_f16s(__fp16 *pL, __fp16 *in, __fp16 *x,
                                  const uint32_t n) {

  uint32_t i, j;
  __fp16 a, b;
  __fp16 c, d;

  __fp16 as, bs;
  __fp16 ax, bx;
  __fp16 diag;

  // Solve for each variable x_i in turn
  for (i = 0; i < n; i++) {
    uint32_t rev_i = (n - 1 - i);
    diag = pL[rev_i * N_BANKS + 2 * rev_i];
    as = (__fp16)in[2 * rev_i];
    bs = (__fp16)in[2 * rev_i + 1];
    // Use the previously solved variables to calculate the sum
    for (j = 0; j < i; j++) {
      uint32_t rev_j = (n - 1 - j);
      a = pL[rev_j * N_BANKS + 2 * rev_i];
      b = pL[rev_j * N_BANKS + 2 * rev_i + 1];
      c = x[2U * rev_j];
      d = x[2U * rev_j + 1];
      asm volatile("fnmsub.h  %[as], %[a], %[c], %[as];"
                   "fnmsub.h  %[as], %[b], %[d], %[as];"
                   "fnmsub.h  %[bs], %[a], %[d], %[bs];"
                   "fmadd.h   %[bs], %[b], %[c], %[bs];"
                   : [as] "+&r"(as), [bs] "+&r"(bs)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                   :);
    }
    // Subtract the sum from b_i and divide by the diagonal element L[i][i]
    asm volatile("fdiv.h %[ax], %[as], %[diag];"
                 "fdiv.h %[bx], %[bs], %[diag];"
                 : [ax] "+&r"(ax), [bx] "+&r"(bx)
                 : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                 :);
    x[2U * rev_i] = ax;
    x[2U * rev_i + 1] = bx;
  }
  return;
}
