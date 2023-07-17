// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define N_BANKS (NUM_CORES * BANKING_FACTOR)

void mempool_cholesky_f32s(float *pSrc, float *pL, const uint32_t n);
void mempool_cholesky_folded_f32s(float *pSrc, float *pL, const uint32_t n);

void mempool_cholesky_f32s(float *pSrc, float *pL, const uint32_t n) {

  register float sum;
  float a, b;
  float c, d;
  float diag;   // Diagonal element
  float ap, bp; // Pivot element
  float as, bs; // Sum element

  uint32_t i, j, k;

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[2U * (j * n + j)];
    sum = 0.0f;
    for (k = 0; k < j; k++) {
      a = pL[2U * (j * n + k)];
      b = pL[2U * (j * n + k) + 1];
      asm volatile("fmadd.s %[sum], %[a], %[a], %[sum];"
                   "fmadd.s %[sum], %[b], %[b], %[sum];"
                   : [sum] "+&r"(sum)
                   : [a] "r"(a), [b] "r"(b)
                   :);
    }
    asm volatile("fsub.s %[ap], %[ap], %[sum];"
                 "fsqrt.s  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
    pL[2U * (j * n + j)] = ap;

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[2U * (i * n + j)];
      bp = pSrc[2U * (i * n + j) + 1];
      // Diag
      diag = pL[2U * (j * n + j)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = 0.0f;
      bs = 0.0f;
      for (k = 0; k < j; k++) {
        a = pL[2U * (i * n + k)];
        b = pL[2U * (i * n + k) + 1];
        c = pL[2U * (j * n + k)];
        d = pL[2U * (j * n + k) + 1];
        asm volatile("fmadd.s %[as], %[a], %[c], %[as];"
                     "fmadd.s %[as], %[b], %[d], %[as];"
                     "fmadd.s %[bs], %[b], %[c], %[bs];"
                     "fnmsub.s %[bs], %[a], %[d], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
      asm volatile("fsub.s %[ap], %[ap], %[as];"
                   "fsub.s %[bp], %[bp], %[bs];"
                   "fdiv.s %[ap], %[ap], %[diag];"
                   "fdiv.s %[bp], %[bp], %[diag];"
                   : [ap] "+&r"(ap), [bp] "+&r"(bp)
                   : [diag] "r"(diag), [as] "r"(as), [bs] "r"(bs)
                   :);
      pL[2U * (i * n + j)] = ap;
      pL[2U * (i * n + j) + 1] = bp;
    }
  }
  return;
}

void mempool_cholesky_folded_f32s(float *pSrc, float *pL, const uint32_t n) {

  register float sum;

  // first matrix row:
  //           item[0-2] item[1-3]
  // memrow[0]    x x       x x
  // memrow[1]    x x       x x
  // second matrix row:
  // memrow[2]    x x       x x
  // memrow[3]    x x       x x
  // third matrix row:
  // memrow[4]    x x       x x
  // memrow[5]    x x       x x
  // i * memrow_xrow * N_BANKS + (j / local_items) * N_BANKS + j % local_items

  float a, b;
  float c, d;
  float diag;   // Diagonal element
  float ap, bp; // Pivot element
  float as, bs; // Sum element
  uint32_t banks_per_row = (n / 2) * N_BANKS;

  uint32_t i, j, k;
  for (j = 0; j < n; j++) {
    // Elements on diagonal (input matrix is positive-definite)
    ap = pSrc[j * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2)];
    sum = 0.0f;
    for (k = 0; k < j; k++) {
      a = pL[j * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2)];
      b = pL[j * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2) + 1];
      asm volatile("fmadd.s %[sum], %[a], %[a], %[sum];"
                   "fmadd.s %[sum], %[b], %[b], %[sum];"
                   : [sum] "+&r"(sum)
                   : [a] "r"(a), [b] "r"(b)
                   :);
    }
    asm volatile("fsub.s %[ap], %[ap], %[sum];"
                 "fsqrt.s  %[ap], %[ap];"
                 : [ap] "+&r"(ap)
                 : [sum] "r"(sum)
                 :);
    pL[j * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2)] = ap;
    // Elements on rows
    for (i = j + 1; i < n; i++) {
      // Pivot
      ap = pSrc[i * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2)];
      bp = pSrc[i * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2) + 1];
      // Diag
      diag = pL[j * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2)];
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      as = 0.0f;
      bs = 0.0f;
      for (k = 0; k < j; k++) {
        a = pL[i * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2)];
        b = pL[i * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2) + 1];
        c = pL[j * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2)];
        d = pL[j * banks_per_row + (k / 2) * N_BANKS + 2 * (k % 2) + 1];
        asm volatile("fmadd.s %[as], %[a], %[c], %[as];"
                     "fmadd.s %[as], %[b], %[d], %[as];"
                     "fmadd.s %[bs], %[b], %[c], %[bs];"
                     "fnmsub.s %[bs], %[a], %[d], %[bs];"
                     : [as] "+&r"(as), [bs] "+&r"(bs)
                     : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d)
                     :);
      }
      asm volatile("fsub.s %[ap], %[ap], %[as];"
                   "fsub.s %[bp], %[bp], %[bs];"
                   "fdiv.s %[ap], %[ap], %[diag];"
                   "fdiv.s %[bp], %[bp], %[diag];"
                   : [ap] "+&r"(ap), [bp] "+&r"(bp)
                   : [diag] "r"(diag), [as] "r"(as), [bs] "r"(bs)
                   :);
      pL[i * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2)] = ap;
      pL[i * banks_per_row + (j / 2) * N_BANKS + 2 * (j % 2) + 1] = bp;
    }
  }
  return;
}
