// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cholesky_q32s(int32_t *pSrc, int32_t *pL, const uint32_t n);
void mempool_lowtrisolver_q32s(int32_t *pL, int32_t *pIn, const uint32_t n);
void mempool_uprtrisolver_q32s(int32_t *pL, int32_t volatile *pIn,
                               const uint32_t n);
void mempool_linearsolver_q32s_schedule(int32_t *pSrc, int32_t *pL,
                                        int32_t volatile *pIn, const uint32_t n,
                                        const uint32_t n_row,
                                        const uint32_t n_col);
void mempool_linearsolver_q32s(int32_t *pSrc, int32_t *pL,
                               int32_t volatile *pIn, const uint32_t n);

void mempool_cholesky_q32s(int32_t *pSrc, int32_t *pL, const uint32_t n) {

  register int32_t sum;
  int32_t pivot, diag, result = 0;
  uint32_t i, j, k;
  int32_t a0 = 0, a1 = 0, a2 = 0, a3 = 0;
  int32_t b0 = 0, b1 = 0, b2 = 0, b3 = 0;

  for (j = 0; j < n; j++) {

    pivot = pSrc[j * n + j];
    sum = 0;
    for (k = 0; k < 4 * (j >> 2U); k++) {
      a0 = pL[j * n + k];
      a1 = pL[j * n + k + 1];
      a2 = pL[j * n + k + 2];
      a3 = pL[j * n + k + 3];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "mul  %[a1],%[a1],%[a1];"
                   "mul  %[a2],%[a2],%[a2];"
                   "mul  %[a3],%[a3],%[a3];"
                   "addi %[a0],%[a0],%[h];"
                   "addi %[a1],%[a1],%[h];"
                   "addi %[a2],%[a2],%[h];"
                   "addi %[a3],%[a3],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "srai  %[a1],%[a1],%[s];"
                   "srai  %[a2],%[a2],%[s];"
                   "srai  %[a3],%[a3],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   "add  %[sum],%[a1],%[sum];"
                   "add  %[sum],%[a2],%[sum];"
                   "add  %[sum],%[a3],%[sum];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                     [a3] "+&r"(a3), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
    }
    switch (j % 4) {
    case 3:
      a0 = pL[j * n + k];
      a1 = pL[j * n + k + 1];
      a2 = pL[j * n + k + 2];
      asm volatile(
          "mul  %[a0],%[a0],%[a0];"
          "mul  %[a1],%[a1],%[a1];"
          "mul  %[a1],%[a2],%[a2];"
          "addi %[a0],%[a0],%[h];"
          "addi %[a1],%[a1],%[h];"
          "addi %[a2],%[a2],%[h];"
          "srai  %[a0],%[a0],%[s];"
          "srai  %[a1],%[a1],%[s];"
          "srai  %[a2],%[a2],%[s];"
          "add  %[sum],%[a0],%[sum];"
          "add  %[sum],%[a1],%[sum];"
          "add  %[sum],%[a2],%[sum];"
          : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
          : [s] "I"(FIXED_POINT), [h] "I"(HALF)
          :);
      break;
    case 2:
      a0 = pL[j * n + k];
      a1 = pL[j * n + k + 1];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "mul  %[a1],%[a1],%[a1];"
                   "addi %[a0],%[a0],%[h];"
                   "addi %[a1],%[a1],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "srai  %[a1],%[a1],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   "add  %[sum],%[a1],%[sum];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 1:
      a0 = pL[j * n + k];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "addi %[a0],%[a0],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   : [a0] "+&r"(a0), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 0:
      break;
    }
    pL[j * n + j] = mempool_sqrt_q32s(pivot - sum);

    for (i = j + 1; i < n; i++) {
      sum = 0;
      pivot = pSrc[i * n + j];
      diag = pL[j * n + j];
      for (k = 0; k < 4 * (j >> 2U); k += 4) {
        a0 = pL[i * n + k];
        b0 = pL[j * n + k];
        a1 = pL[i * n + k + 1];
        b1 = pL[j * n + k + 1];
        a2 = pL[i * n + k + 2];
        b2 = pL[j * n + k + 2];
        a3 = pL[i * n + k + 3];
        b3 = pL[j * n + k + 3];
        //                    idx_a = (uint32_t) &(pL[i * n + k]);
        //                    idx_b = (uint32_t) &(pL[j * n + k]);
        asm volatile(
            //                    "lw  %[a0],0(%[idx_a]);"
            //                    "lw  %[b0],0(%[idx_b]);"
            //                    "lw  %[a1],4(%[idx_a]);"
            //                    "lw  %[b1],4(%[idx_b]);"
            //                    "lw  %[a2],8(%[idx_a]);"
            //                    "lw  %[b2],8(%[idx_b]);"
            //                    "lw  %[a3],12(%[idx_a]);"
            //                    "lw  %[b3],12(%[idx_b]);"
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "mul  %[a2],%[a2],%[b2];"
            "mul  %[a3],%[a3],%[b3];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "addi %[a2],%[a2],%[h];"
            "addi %[a3],%[a3],%[h];"
            "srai  %[a0],%[a0],%[s];"
            "srai  %[a1],%[a1],%[s];"
            "srai  %[a2],%[a2],%[s];"
            "srai  %[a3],%[a3],%[s];"
            "add  %[sum],%[a0],%[sum];"
            "add  %[sum],%[a1],%[sum];"
            "add  %[sum],%[a2],%[sum];"
            "add  %[sum],%[a3],%[sum];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [a3] "+&r"(a3),
              // [sum] "+&r" (sum), [idx_a] "+&r" (idx_a), [idx_b] "+&r" (idx_b)
              [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3),
              [s] "I"(FIXED_POINT), [h] "I"(HALF)
            : "memory");
      }
      switch (j % 4) {
      case 3:
        a0 = pL[i * n + k];
        b0 = pL[j * n + k];
        a1 = pL[i * n + k + 1];
        b1 = pL[j * n + k + 1];
        a2 = pL[i * n + k + 2];
        b3 = pL[j * n + k + 2];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "mul  %[a1],%[a2],%[b2];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "addi %[a2],%[a2],%[h];"
            "srai  %[a0],%[a0],%[s];"
            "srai  %[a1],%[a1],%[s];"
            "srai  %[a2],%[a2],%[s];"
            "add  %[sum],%[a0],%[sum];"
            "add  %[sum],%[a1],%[sum];"
            "add  %[sum],%[a2],%[sum];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [s] "I"(FIXED_POINT),
              [h] "I"(HALF)
            :);
        break;
      case 2:
        a0 = pL[i * n + k];
        b0 = pL[j * n + k];
        a1 = pL[i * n + k + 1];
        b1 = pL[j * n + k + 1];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "srai  %[a0],%[a0],%[s];"
            "srai  %[a1],%[a1],%[s];"
            "add  %[sum],%[a0],%[sum];"
            "add  %[sum],%[a1],%[sum];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [s] "I"(FIXED_POINT), [h] "I"(HALF)
            :);
        break;
      case 1:
        a0 = pL[i * n + k];
        b0 = pL[j * n + k];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "addi %[a0],%[a0],%[h];"
                     "srai  %[a0],%[a0],%[s];"
                     "add  %[sum],%[a0],%[sum];"
                     : [a0] "+&r"(a0), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
        break;
      case 0:
        break;
      }
      if (i >= (j + 2))
        pL[(i - 1) * n + j] = result;
      result = FIX_DIV((pivot - sum), diag);
    }
    pL[(i - 1) * n + j] = result;
  }
}

void mempool_linearsolver_q32s_schedule(int32_t *pSrc, int32_t *pL,
                                        int32_t volatile *pIn, const uint32_t n,
                                        const uint32_t n_row,
                                        const uint32_t n_col) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t idx_row, idx_col = core_id;
  for (idx_row = 0; idx_row < n_row; idx_row++) {
    mempool_linearsolver_q32s(pSrc + idx_col * n,
                              pL + idx_col * n + idx_row * N_BANKS,
                              pIn + idx_col * n, n);
    mempool_uprtrisolver_q32s(pL + idx_col * n + idx_row * N_BANKS,
                              pIn + idx_col * n, n);
  }
  // mempool_log_partial_barrier(2, core_id, n_col * (n >> 2U));
}

void mempool_linearsolver_q32s(int32_t *pSrc, int32_t *pL,
                               int32_t volatile *pIn, const uint32_t n) {

  int32_t sum;
  int32_t sum_r;
  int32_t in;

  int32_t pivot, diag, result = 0;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  for (j = 0; j < n; j++) {
    in = pIn[j];
    pivot = pSrc[j * N_BANKS + j];
    sum = 0;
    for (k = 0; k < 4 * (j >> 2U); k++) {
      a0 = pL[j * N_BANKS + k];
      a1 = pL[j * N_BANKS + k + 1];
      a2 = pL[j * N_BANKS + k + 2];
      a3 = pL[j * N_BANKS + k + 3];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "mul  %[a1],%[a1],%[a1];"
                   "mul  %[a2],%[a2],%[a2];"
                   "mul  %[a3],%[a3],%[a3];"
                   "addi %[a0],%[a0],%[h];"
                   "addi %[a1],%[a1],%[h];"
                   "addi %[a2],%[a2],%[h];"
                   "addi %[a3],%[a3],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "srai  %[a1],%[a1],%[s];"
                   "srai  %[a2],%[a2],%[s];"
                   "srai  %[a3],%[a3],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   "add  %[sum],%[a1],%[sum];"
                   "add  %[sum],%[a2],%[sum];"
                   "add  %[sum],%[a3],%[sum];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                     [a3] "+&r"(a3), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
    }
    switch (j % 4) {
    case 3:
      a0 = pL[j * N_BANKS + k];
      a1 = pL[j * N_BANKS + k + 1];
      a2 = pL[j * N_BANKS + k + 2];
      asm volatile(
          "mul  %[a0],%[a0],%[a0];"
          "mul  %[a1],%[a1],%[a1];"
          "mul  %[a2],%[a2],%[a2];"
          "addi %[a0],%[a0],%[h];"
          "addi %[a1],%[a1],%[h];"
          "addi %[a2],%[a2],%[h];"
          "srai  %[a0],%[a0],%[s];"
          "srai  %[a1],%[a1],%[s];"
          "srai  %[a2],%[a2],%[s];"
          "add  %[sum],%[a0],%[sum];"
          "add  %[sum],%[a1],%[sum];"
          "add  %[sum],%[a2],%[sum];"
          : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
          : [s] "I"(FIXED_POINT), [h] "I"(HALF)
          :);
      break;
    case 2:
      a0 = pL[j * N_BANKS + k];
      a1 = pL[j * N_BANKS + k + 1];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "mul  %[a1],%[a1],%[a1];"
                   "addi %[a0],%[a0],%[h];"
                   "addi %[a1],%[a1],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "srai  %[a1],%[a1],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   "add  %[sum],%[a1],%[sum];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 1:
      a0 = pL[j * N_BANKS + k];
      asm volatile("mul  %[a0],%[a0],%[a0];"
                   "addi %[a0],%[a0],%[h];"
                   "srai  %[a0],%[a0],%[s];"
                   "add  %[sum],%[a0],%[sum];"
                   : [a0] "+&r"(a0), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 0:
      break;
    }
    diag = mempool_sqrt_q32s(pivot - sum);
    in = FIX_DIV(in, diag);

    sum_r = 0;
    for (i = j + 1; i < n; i++) {
      pivot = pSrc[i * N_BANKS + j];
      sum = 0;
      k = 0;
      while (k < 4 * (j >> 2U)) {
        a0 = pL[i * N_BANKS + k];
        b0 = pL[j * N_BANKS + k];
        a1 = pL[i * N_BANKS + k + 1];
        b1 = pL[j * N_BANKS + k + 1];
        a2 = pL[i * N_BANKS + k + 2];
        b2 = pL[j * N_BANKS + k + 2];
        a3 = pL[i * N_BANKS + k + 3];
        b3 = pL[j * N_BANKS + k + 3];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "mul  %[a1],%[a1],%[b1];"
                     "mul  %[a2],%[a2],%[b2];"
                     "mul  %[a3],%[a3],%[b3];"
                     "addi %[a0],%[a0],%[h];"
                     "addi %[a1],%[a1],%[h];"
                     "addi %[a2],%[a2],%[h];"
                     "addi %[a3],%[a3],%[h];"
                     "srai  %[a0],%[a0],%[s];"
                     "srai  %[a1],%[a1],%[s];"
                     "srai  %[a2],%[a2],%[s];"
                     "srai  %[a3],%[a3],%[s];"
                     "add  %[sum],%[a0],%[sum];"
                     "add  %[sum],%[a1],%[sum];"
                     "add  %[sum],%[a2],%[sum];"
                     "add  %[sum],%[a3],%[sum];"
                     : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                       [a3] "+&r"(a3), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3),
                       [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     : "memory");
        k += 4;
      }
      switch (j % 4) {
      case 3:
        a0 = pL[i * N_BANKS + k];
        b0 = pL[j * N_BANKS + k];
        a1 = pL[i * N_BANKS + k + 1];
        b1 = pL[j * N_BANKS + k + 1];
        a2 = pL[i * N_BANKS + k + 2];
        b2 = pL[j * N_BANKS + k + 2];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "mul  %[a2],%[a2],%[b2];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "addi %[a2],%[a2],%[h];"
            "srai  %[a0],%[a0],%[s];"
            "srai  %[a1],%[a1],%[s];"
            "srai  %[a2],%[a2],%[s];"
            "add  %[sum],%[a0],%[sum];"
            "add  %[sum],%[a1],%[sum];"
            "add  %[sum],%[a2],%[sum];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [s] "I"(FIXED_POINT),
              [h] "I"(HALF)
            :);
        break;
      case 2:
        a0 = pL[i * N_BANKS + k];
        b0 = pL[j * N_BANKS + k];
        a1 = pL[i * N_BANKS + k + 1];
        b1 = pL[j * N_BANKS + k + 1];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "srai  %[a0],%[a0],%[s];"
            "srai  %[a1],%[a1],%[s];"
            "add  %[sum],%[a0],%[sum];"
            "add  %[sum],%[a1],%[sum];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [s] "I"(FIXED_POINT), [h] "I"(HALF)
            :);
        break;
      case 1:
        a0 = pL[i * N_BANKS + k];
        b0 = pL[j * N_BANKS + k];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "addi %[a0],%[a0],%[h];"
                     "srai  %[a0],%[a0],%[s];"
                     "add  %[sum],%[a0],%[sum];"
                     : [a0] "+&r"(a0), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
        break;
      case 0:
        break;
      }
      if (i > (j + 1)) {
        sum_r = pIn[i - 1];
        pL[(i - 1) * N_BANKS + j] = result;
        pIn[i - 1] = sum_r - (((result * in) + HALF) >> FIXED_POINT);
      }
      result = FIX_DIV((pivot - sum), diag);
    }
    if (j < (n - 1)) {
      sum_r = pIn[i - 1];
      pL[(n - 1) * N_BANKS + j] = result;
      pIn[n - 1] = sum_r - (((result * in) + HALF) >> FIXED_POINT);
    }
    pIn[j] = in;
    pL[j * N_BANKS + j] = diag;
  }
}

void mempool_uprtrisolver_q32s(int32_t *pL, int32_t volatile *pIn,
                               const uint32_t n) {

  uint32_t i, j;
  int32_t sum;
  int32_t in0, in1, in2, in3;
  int32_t l0, l1, l2, l3;

  for (i = n - 1; i < n; i--) {
    sum = pIn[i];
    for (j = 0; j < 4 * ((n - 1 - i) >> 2U); j += 4) {
      l0 = pL[(n - 1 - j) * N_BANKS + i];
      l1 = pL[(n - 1 - j - 1) * N_BANKS + i];
      l2 = pL[(n - 1 - j - 2) * N_BANKS + i];
      l3 = pL[(n - 1 - j - 3) * N_BANKS + i];
      in0 = pIn[n - 1 - j];
      in1 = pIn[n - 1 - j - 1];
      in2 = pIn[n - 1 - j - 2];
      in3 = pIn[n - 1 - j - 3];
      asm volatile("mul  %[in0],%[in0],%[l0];"
                   "mul  %[in1],%[in1],%[l1];"
                   "mul  %[in2],%[in2],%[l2];"
                   "mul  %[in3],%[in3],%[l3];"
                   "addi %[in0],%[in0],%[h];"
                   "addi %[in1],%[in1],%[h];"
                   "addi %[in2],%[in2],%[h];"
                   "addi %[in3],%[in3],%[h];"
                   "srai %[in0],%[in0],%[s];"
                   "srai %[in1],%[in1],%[s];"
                   "srai %[in2],%[in2],%[s];"
                   "srai %[in3],%[in3],%[s];"
                   "sub  %[sum],%[sum],%[in0];"
                   "sub  %[sum],%[sum],%[in1];"
                   "sub  %[sum],%[sum],%[in2];"
                   "sub  %[sum],%[sum],%[in3];"
                   : [in0] "+&r"(in0), [in1] "+&r"(in1), [in2] "+&r"(in2),
                     [in3] "+&r"(in3), [sum] "+&r"(sum)
                   : [l0] "r"(l0), [l1] "r"(l1), [l2] "r"(l2), [l3] "r"(l3),
                     [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
    }
    switch ((n - i) % 4) {
    case 3:
      l0 = pL[(n - 1 - j) * N_BANKS + i];
      l1 = pL[(n - 1 - j - 1) * N_BANKS + i];
      l2 = pL[(n - 1 - j - 2) * N_BANKS + i];
      in0 = pIn[n - 1 - j];
      in1 = pIn[n - 1 - j - 1];
      in2 = pIn[n - 1 - j - 2];
      asm volatile("mul  %[in0],%[in0],%[l0];"
                   "mul  %[in1],%[in1],%[l1];"
                   "mul  %[in2],%[in2],%[l2];"
                   "addi %[in0],%[in0],%[h];"
                   "addi %[in1],%[in1],%[h];"
                   "addi %[in2],%[in2],%[h];"
                   "srai %[in0],%[in0],%[s];"
                   "srai %[in1],%[in1],%[s];"
                   "srai %[in2],%[in2],%[s];"
                   "sub  %[sum],%[sum],%[in0];"
                   "sub  %[sum],%[sum],%[in1];"
                   "sub  %[sum],%[sum],%[in2];"
                   : [in0] "+&r"(in0), [in1] "+&r"(in1), [in2] "+&r"(in2),
                     [sum] "+&r"(sum)
                   : [l0] "r"(l0), [l1] "r"(l1), [l2] "r"(l2),
                     [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 2:
      l0 = pL[(n - 1 - j) * N_BANKS + i];
      l1 = pL[(n - 1 - j - 1) * N_BANKS + i];
      in0 = pIn[n - 1 - j];
      in1 = pIn[n - 1 - j - 1];
      asm volatile(
          "mul  %[in0],%[in0],%[l0];"
          "mul  %[in1],%[in1],%[l1];"
          "addi %[in0],%[in0],%[h];"
          "addi %[in1],%[in1],%[h];"
          "srai %[in0],%[in0],%[s];"
          "srai %[in1],%[in1],%[s];"
          "sub  %[sum],%[sum],%[in0];"
          "sub  %[sum],%[sum],%[in1];"
          : [in0] "+&r"(in0), [in1] "+&r"(in1), [sum] "+&r"(sum)
          : [l0] "r"(l0), [l1] "r"(l1), [s] "I"(FIXED_POINT), [h] "I"(HALF)
          :);
      break;
    case 1:
      l0 = pL[(n - 1 - j) * N_BANKS + i];
      in0 = pIn[n - 1 - j];
      asm volatile("mul  %[in0],%[in0],%[l0];"
                   "addi %[in0],%[in0],%[h];"
                   "srai %[in0],%[in0],%[s];"
                   "sub  %[sum],%[sum],%[in0];"
                   : [in0] "+&r"(in0), [sum] "+&r"(sum)
                   : [l0] "r"(l0), [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 0:
      break;
    }
    pIn[i] = FIX_DIV(sum, pL[i * N_BANKS + i]);
  }
}
