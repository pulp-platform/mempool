// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cholesky_q32s(int32_t *pSrc, int32_t *pL, const uint32_t n);

void mempool_cholesky_q32s_schedule(int32_t *pSrc, int32_t *pL,
                                    const uint32_t n, const uint32_t n_row,
                                    const uint32_t n_col);

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

void mempool_cholesky_q32s_schedule(int32_t *pSrc, int32_t *pL,
                                    const uint32_t n, const uint32_t n_row,
                                    const uint32_t n_col) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t idx_row, idx_col = core_id;
  for (idx_row = 0; idx_row < n_row; idx_row++) {
    mempool_cholesky_q32s(pSrc + idx_col * n,
                          pL + idx_col * n + idx_row * N_BANKS, n);
  }
  mempool_log_partial_barrier(2, core_id, n_col * (n >> 2U));
}
