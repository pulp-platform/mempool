// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cholesky_q32p(int32_t *pSrc, int32_t *pL, const uint32_t n);

void mempool_cholesky_q32p_foldleft(int32_t *pSrc, int32_t *pL,
                                    const uint32_t n, const uint32_t nPE);

void mempool_cholesky_q32p_foldright(int32_t *pSrc, int32_t *pL,
                                     const uint32_t n, const uint32_t nPE);

void mempool_cholesky_q32p_fold(int32_t *pSrcA, int32_t *pSrcB, int32_t *pLL,
                                int32_t *pLR, const uint32_t n,
                                const uint32_t nPE);

void mempool_linearsolver_q32p_fold(int32_t *pSrcA, int32_t *pSrcB,
                                    int32_t *pLL, int32_t *pLR, int32_t *pInA,
                                    int32_t *pInB, const uint32_t n,
                                    const uint32_t nPE);

void mempool_cholesky_q32p(int32_t *pSrc, int32_t *pL, const uint32_t n) {

  int32_t sum;
  int32_t pivot, diag;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t row_id;
  if (absolute_core_id % n == 0)
    row_id = absolute_core_id / n;
  else
    row_id = n + 1;

  for (j = 0; j < n; j++) {

    /* Elements on the diagonal are computed with a single core */
    if (row_id == (j % NUM_CORES)) {
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
    }
    mempool_log_barrier(2, absolute_core_id);

    if (row_id >= (j + 1)) {
      for (i = row_id; i < n; i += NUM_CORES) {
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
        }
        switch (j % 4) {
        case 3:
          a0 = pL[i * n + k];
          b0 = pL[j * n + k];
          a1 = pL[i * n + k + 1];
          b1 = pL[j * n + k + 1];
          a2 = pL[i * n + k + 2];
          b2 = pL[j * n + k + 2];
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
        pL[i * n + j] = FIX_DIV((pivot - sum), diag);
      }
    }
    mempool_log_barrier(2, absolute_core_id);
  }
}

void mempool_cholesky_q32p_foldleft(int32_t *pSrc, int32_t *pL,
                                    const uint32_t n, const uint32_t nPE) {

  int32_t sum;
  int32_t pivot, diag;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (n >> 2U);

  for (j = 0; j < n; j++) {
    /* Elements on the diagonal are computed with a single core */
    if (core_id == (j >> 2U)) {
      pivot = pSrc[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pL[j + k * N_BANKS];
        a1 = pL[j + (k + 1) * N_BANKS];
        a2 = pL[j + (k + 2) * N_BANKS];
        a3 = pL[j + (k + 3) * N_BANKS];
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
        a0 = pL[j + k * N_BANKS];
        a1 = pL[j + (k + 1) * N_BANKS];
        a2 = pL[j + (k + 2) * N_BANKS];
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
        a0 = pL[j + k * N_BANKS];
        a1 = pL[j + (k + 1) * N_BANKS];
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
        a0 = pL[j + k * N_BANKS];
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
      pL[j * N_BANKS + j] = mempool_sqrt_q32s(pivot - sum);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == (i / 4)) {
        sum = 0;
        pivot = pSrc[i * n + j];
        diag = pL[j + j * N_BANKS];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pL[i + k * N_BANKS];
          a1 = pL[i + (k + 1) * N_BANKS];
          a2 = pL[i + (k + 2) * N_BANKS];
          a3 = pL[i + (k + 3) * N_BANKS];
          b0 = pL[j + k * N_BANKS];
          b1 = pL[j + (k + 1) * N_BANKS];
          b2 = pL[j + (k + 2) * N_BANKS];
          b3 = pL[j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pL[i + k * N_BANKS];
          a1 = pL[i + (k + 1) * N_BANKS];
          a2 = pL[i + (k + 2) * N_BANKS];
          b0 = pL[j + k * N_BANKS];
          b1 = pL[j + (k + 1) * N_BANKS];
          b2 = pL[j + (k + 2) * N_BANKS];
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
          a0 = pL[i + k * N_BANKS];
          a1 = pL[i + (k + 1) * N_BANKS];
          b0 = pL[j + k * N_BANKS];
          b1 = pL[j + (k + 1) * N_BANKS];
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
          a0 = pL[i + k * N_BANKS];
          b0 = pL[j + k * N_BANKS];
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
        pL[i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
}

void mempool_cholesky_q32p_foldright(int32_t *pSrc, int32_t *pL,
                                     const uint32_t n, const uint32_t nPE) {

  int32_t sum;
  int32_t pivot, diag;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (n >> 2U);

  for (j = 0; j < n; j++) {
    /* Elements on the diagonal are computed with a single core */
    if (core_id == nPE - 1 - (j >> 2U)) {
      pivot = pSrc[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pL[n - 1 - j + k * N_BANKS];
        a1 = pL[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pL[n - 1 - j + (k + 2) * N_BANKS];
        a3 = pL[n - 1 - j + (k + 3) * N_BANKS];
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
        a0 = pL[n - 1 - j + k * N_BANKS];
        a1 = pL[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pL[n - 1 - j + (k + 2) * N_BANKS];
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
        a0 = pL[n - 1 - j + k * N_BANKS];
        a1 = pL[n - 1 - j + (k + 1) * N_BANKS];
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
        a0 = pL[n - 1 - j + k * N_BANKS];
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
      pL[j * N_BANKS + n - 1 - j] = mempool_sqrt_q32s(pivot - sum);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == nPE - 1 - (i / 4)) {
        sum = 0;
        pivot = pSrc[i * n + j];
        diag = pL[n - 1 - j + j * N_BANKS];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pL[n - 1 - i + k * N_BANKS];
          a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pL[n - 1 - i + (k + 2) * N_BANKS];
          a3 = pL[n - 1 - i + (k + 3) * N_BANKS];
          b0 = pL[n - 1 - j + k * N_BANKS];
          b1 = pL[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pL[n - 1 - j + (k + 2) * N_BANKS];
          b3 = pL[n - 1 - j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pL[n - 1 - i + k * N_BANKS];
          a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pL[n - 1 - i + (k + 2) * N_BANKS];
          b0 = pL[n - 1 - j + k * N_BANKS];
          b1 = pL[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pL[n - 1 - j + (k + 2) * N_BANKS];
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
          a0 = pL[n - 1 - i + k * N_BANKS];
          a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
          b0 = pL[n - 1 - j + k * N_BANKS];
          b1 = pL[n - 1 - j + (k + 1) * N_BANKS];
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
          a0 = pL[n - 1 - i + k * N_BANKS];
          b0 = pL[n - 1 - j + k * N_BANKS];
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
        pL[n - 1 - i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
}

void mempool_cholesky_q32p_fold(int32_t *pSrcA, int32_t *pSrcB, int32_t *pLL,
                                int32_t *pLR, const uint32_t n,
                                const uint32_t nPE) {

  int32_t sum;
  int32_t pivot, diag;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (n >> 2U);

  for (j = 0; j < n; j++) {
    /* LEFT */
    /* Elements on the diagonal are computed with a single core */
    if (core_id == (j >> 2U)) {
      pivot = pSrcA[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
        a2 = pLL[j + (k + 2) * N_BANKS];
        a3 = pLL[j + (k + 3) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
        a2 = pLL[j + (k + 2) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
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
      pLL[j * N_BANKS + j] = mempool_sqrt_q32s(pivot - sum);
    }
    /* RIGHT */
    /* Elements on the diagonal are computed with a single core */
    if (core_id == nPE - 1 - (j >> 2U)) {
      pivot = pSrcB[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
        a3 = pLR[n - 1 - j + (k + 3) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
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
      pLR[j * N_BANKS + n - 1 - j] = mempool_sqrt_q32s(pivot - sum);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
    /* LEFT */
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == (i / 4)) {
        sum = 0;
        pivot = pSrcA[i * n + j];
        diag = pLL[j + j * N_BANKS];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          a2 = pLL[i + (k + 2) * N_BANKS];
          a3 = pLL[i + (k + 3) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
          b2 = pLL[j + (k + 2) * N_BANKS];
          b3 = pLL[j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          a2 = pLL[i + (k + 2) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
          b2 = pLL[j + (k + 2) * N_BANKS];
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
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
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
          a0 = pLL[i + k * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
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
        pLL[i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
      }
    }
    /* RIGHT */
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == nPE - 1 - (i / 4)) {
        sum = 0;
        pivot = pSrcB[i * n + j];
        diag = pLR[n - 1 - j + j * N_BANKS];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pLR[n - 1 - i + (k + 2) * N_BANKS];
          a3 = pLR[n - 1 - i + (k + 3) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
          b3 = pLR[n - 1 - j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pLR[n - 1 - i + (k + 2) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
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
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
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
          a0 = pLR[n - 1 - i + k * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
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
        pLR[n - 1 - i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
}

void mempool_linearsolver_q32p_fold(int32_t *pSrcA, int32_t *pSrcB,
                                    int32_t *pLL, int32_t *pLR, int32_t *pInA,
                                    int32_t *pInB, const uint32_t n,
                                    const uint32_t nPE) {

  int32_t sum, sum_r, in, result;
  int32_t pivot, diag;
  uint32_t i, j, k;
  int32_t a0, a1, a2, a3;
  int32_t b0, b1, b2, b3;

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id % (n >> 2U);

  for (j = 0; j < n; j++) {
    /* LEFT */
    /* Elements on the diagonal are computed with a single core */
    if (core_id == (j >> 2U)) {
      in = pInA[j];
      pivot = pSrcA[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
        a2 = pLL[j + (k + 2) * N_BANKS];
        a3 = pLL[j + (k + 3) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
        a2 = pLL[j + (k + 2) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
        a1 = pLL[j + (k + 1) * N_BANKS];
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
        a0 = pLL[j + k * N_BANKS];
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
      result = mempool_sqrt_q32s(pivot - sum);
      pInA[j] = FIX_DIV(in, result);
      pLL[j * N_BANKS + j] = result;
    }
    /* RIGHT */
    /* Elements on the diagonal are computed with a single core */
    if (core_id == nPE - 1 - (j >> 2U)) {
      in = pInB[j];
      pivot = pSrcB[j * n + j];
      sum = 0;
      for (k = 0; k < 4 * (j >> 2U); k++) {
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
        a3 = pLR[n - 1 - j + (k + 3) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
        a2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
        a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
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
        a0 = pLR[n - 1 - j + k * N_BANKS];
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
      result = mempool_sqrt_q32s(pivot - sum);
      pInB[j] = FIX_DIV(in, result);
      pLR[j * N_BANKS + n - 1 - j] = result;
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
    /* LEFT */
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == (i / 4)) {
        sum = 0;
        pivot = pSrcA[i * n + j];
        diag = pLL[j + j * N_BANKS];
        in = pInA[j];
        sum_r = pInA[i];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          a2 = pLL[i + (k + 2) * N_BANKS];
          a3 = pLL[i + (k + 3) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
          b2 = pLL[j + (k + 2) * N_BANKS];
          b3 = pLL[j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          a2 = pLL[i + (k + 2) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
          b2 = pLL[j + (k + 2) * N_BANKS];
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
          a0 = pLL[i + k * N_BANKS];
          a1 = pLL[i + (k + 1) * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
          b1 = pLL[j + (k + 1) * N_BANKS];
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
          a0 = pLL[i + k * N_BANKS];
          b0 = pLL[j + k * N_BANKS];
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
        result = FIX_DIV((pivot - sum), diag);
        pLL[i + j * N_BANKS] = result;
        pInA[i] = sum_r - result * in;
      }
    }
    /* RIGHT */
    /* Elements on rows are computed in parallel, each core gets 4 rows */
    for (i = j + 1; i < n; i++) {
      if (core_id == nPE - 1 - (i / 4)) {
        sum = 0;
        pivot = pSrcB[i * n + j];
        diag = pLR[n - 1 - j + j * N_BANKS];
        in = pInB[j];
        sum_r = pInB[i];
        for (k = 0; k < 4 * (j >> 2U); k += 4) {
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pLR[n - 1 - i + (k + 2) * N_BANKS];
          a3 = pLR[n - 1 - i + (k + 3) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
          b3 = pLR[n - 1 - j + (k + 3) * N_BANKS];
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
                       :);
        }
        switch (j % 4) {
        case 3:
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          a2 = pLR[n - 1 - i + (k + 2) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
          b2 = pLR[n - 1 - j + (k + 2) * N_BANKS];
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
          a0 = pLR[n - 1 - i + k * N_BANKS];
          a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
          b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
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
          a0 = pLR[n - 1 - i + k * N_BANKS];
          b0 = pLR[n - 1 - j + k * N_BANKS];
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
        result = FIX_DIV((pivot - sum), diag);
        pLR[n - 1 - i + j * N_BANKS] = result;
        pInB[i] = sum_r - result * in;
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
  }
  if (core_id == 0) {
    /* LEFT */
    for (i = n - 1; i < n; i--) {
      sum = pInA[i];
      for (j = n - 1; j >= (4 * (i >> 2U) + 4); j -= 4) {
        a0 = pInA[j];
        a1 = pInA[j - 1];
        a2 = pInA[j - 2];
        a3 = pInA[j - 3];
        b0 = pLL[j + i * N_BANKS];
        b1 = pLL[(j - 1) + i * N_BANKS];
        b2 = pLL[(j - 2) + i * N_BANKS];
        b3 = pLL[(j - 3) + i * N_BANKS];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "mul  %[a1],%[a1],%[b1];"
                     "mul  %[a2],%[a2],%[b2];"
                     "mul  %[a3],%[a3],%[b3];"
                     "addi %[a0],%[a0],%[h];"
                     "addi %[a1],%[a1],%[h];"
                     "addi %[a2],%[a2],%[h];"
                     "addi %[a3],%[a3],%[h];"
                     "srai %[a0],%[a0],%[s];"
                     "srai %[a1],%[a1],%[s];"
                     "srai %[a2],%[a2],%[s];"
                     "srai %[a3],%[a3],%[s];"
                     "sub  %[sum],%[sum],%[a0];"
                     "sub  %[sum],%[sum],%[a1];"
                     "sub  %[sum],%[sum],%[a2];"
                     "sub  %[sum],%[sum],%[a3];"
                     : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                       [a3] "+&r"(a3), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3),
                       [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
      }
      switch (i % 4) {
      case 1:
        a0 = pInA[j];
        a1 = pInA[j - 1];
        a2 = pInA[j - 2];
        b0 = pLL[j + i * N_BANKS];
        b1 = pLL[(j - 1) + i * N_BANKS];
        b2 = pLL[(j - 2) + i * N_BANKS];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "mul  %[a2],%[a2],%[b2];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "addi %[a2],%[a2],%[h];"
            "srai %[a0],%[a0],%[s];"
            "srai %[a1],%[a1],%[s];"
            "srai %[a2],%[a2],%[s];"
            "sub  %[sum],%[sum],%[a0];"
            "sub  %[sum],%[sum],%[a1];"
            "sub  %[sum],%[sum],%[a2];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [s] "I"(FIXED_POINT),
              [h] "I"(HALF)
            :);
        break;
      case 2:
        a0 = pInA[j];
        a1 = pInA[j - 1];
        b0 = pLL[j + i * N_BANKS];
        b1 = pLL[(j - 1) + i * N_BANKS];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "srai %[a0],%[a0],%[s];"
            "srai %[a1],%[a1],%[s];"
            "sub  %[sum],%[sum],%[a0];"
            "sub  %[sum],%[sum],%[a1];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [s] "I"(FIXED_POINT), [h] "I"(HALF)
            :);
        break;
      case 3:
        a0 = pInA[j];
        b0 = pLL[j + i * N_BANKS];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "addi %[a0],%[a0],%[h];"
                     "srai %[a0],%[a0],%[s];"
                     "sub  %[sum],%[sum],%[a0];"
                     : [a0] "+&r"(a0), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
        break;
      case 0:
        break;
      }
      pInA[i] = FIX_DIV(sum, pLL[i * N_BANKS + i]);
    }
  }
  /* RIGHT */
  if (core_id == nPE - 1) {
    for (i = n - 1; i < n; i++) {
      sum = pInB[i];
      for (j = 0; j < 4 * ((n - i) >> 2U); j += 4) {
        a0 = pInB[n - 1 - j];
        a1 = pInB[n - 1 - j - 1];
        a2 = pInB[n - 1 - j - 2];
        a3 = pInB[n - 1 - j - 3];
        b0 = pLR[j + i * N_BANKS];
        b1 = pLR[(j + 1) + i * N_BANKS];
        b2 = pLR[(j + 2) + i * N_BANKS];
        b3 = pLR[(j + 3) + i * N_BANKS];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "mul  %[a1],%[a1],%[b1];"
                     "mul  %[a2],%[a2],%[b2];"
                     "mul  %[a3],%[a3],%[b3];"
                     "addi %[a0],%[a0],%[h];"
                     "addi %[a1],%[a1],%[h];"
                     "addi %[a2],%[a2],%[h];"
                     "addi %[a3],%[a3],%[h];"
                     "srai %[a0],%[a0],%[s];"
                     "srai %[a1],%[a1],%[s];"
                     "srai %[a2],%[a2],%[s];"
                     "srai %[a3],%[a3],%[s];"
                     "sub  %[sum],%[sum],%[a0];"
                     "sub  %[sum],%[sum],%[a1];"
                     "sub  %[sum],%[sum],%[a2];"
                     "sub  %[sum],%[sum],%[a3];"
                     : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                       [a3] "+&r"(a3), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3),
                       [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
      }
      switch ((n - i) % 4) {
      case 3:
        a0 = pInB[n - 1 - j];
        a1 = pInB[n - 1 - j - 1];
        a2 = pInB[n - 1 - j - 2];
        b0 = pLR[j + i * N_BANKS];
        b1 = pLR[(j + 1) + i * N_BANKS];
        b2 = pLR[(j + 2) + i * N_BANKS];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "mul  %[a2],%[a2],%[b2];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "addi %[a2],%[a2],%[h];"
            "srai %[a0],%[a0],%[s];"
            "srai %[a1],%[a1],%[s];"
            "srai %[a2],%[a2],%[s];"
            "sub  %[sum],%[sum],%[a0];"
            "sub  %[sum],%[sum],%[a1];"
            "sub  %[sum],%[sum],%[a2];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [s] "I"(FIXED_POINT),
              [h] "I"(HALF)
            :);
        break;
      case 2:
        a0 = pInB[n - 1 - j];
        a1 = pInB[n - 1 - j - 1];
        b0 = pLR[j + i * N_BANKS];
        b1 = pLR[(j + 1) + i * N_BANKS];
        asm volatile(
            "mul  %[a0],%[a0],%[b0];"
            "mul  %[a1],%[a1],%[b1];"
            "addi %[a0],%[a0],%[h];"
            "addi %[a1],%[a1],%[h];"
            "srai %[a0],%[a0],%[s];"
            "srai %[a1],%[a1],%[s];"
            "sub  %[sum],%[sum],%[a0];"
            "sub  %[sum],%[sum],%[a1];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
            : [b0] "r"(b0), [b1] "r"(b1), [s] "I"(FIXED_POINT), [h] "I"(HALF)
            :);
        break;
      case 1:
        a0 = pInB[n - 1 - j];
        b0 = pLR[j + i * N_BANKS];
        asm volatile("mul  %[a0],%[a0],%[b0];"
                     "addi %[a0],%[a0],%[h];"
                     "srai %[a0],%[a0],%[s];"
                     "sub  %[sum],%[sum],%[a0];"
                     : [a0] "+&r"(a0), [sum] "+&r"(sum)
                     : [b0] "r"(b0), [s] "I"(FIXED_POINT), [h] "I"(HALF)
                     :);
        break;
      case 0:
        break;
      }
      pInB[i] = FIX_DIV(sum, pLR[i * N_BANKS + i]);
    }
  }
  mempool_log_partial_barrier(2, absolute_core_id, nPE);
}
