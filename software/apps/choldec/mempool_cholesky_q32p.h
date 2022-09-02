// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

dump(id, 1);

void mempool_cholesky_q32p(int32_t* pSrc,
                           int32_t* pL,
                           const uint32_t n,
                           const uint32_t fracBits);

void mempool_cholesky_q32p_foldleft(int32_t* pSrc,
                                    int32_t* pL,
                                    const uint32_t n,
                                    const uint32_t fracBits,
                                    const uint32_t nPE);

void mempool_cholesky_q32p_foldright(int32_t* pSrc,
                                     int32_t* pL,
                                     const uint32_t n,
                                     const uint32_t fracBits,
                                     const uint32_t nPE);

void mempool_cholesky_q32p_fold(int32_t* pSrcA,
                                int32_t* pSrcB,
                                int32_t* pLL,
                                int32_t* pLR,
                                const uint32_t n,
                                const uint32_t fracBits,
                                const uint32_t nPE);

void mempool_cholesky_q32p(int32_t* pSrc,
                           int32_t* pL,
                           const uint32_t n,
                           const uint32_t fracBits) {

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
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
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
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pL[j * n + k];
                a1 = pL[j * n + k + 1];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pL[j * n + k];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k++;
            }
            pL[j * n + j] = mempool_sqrt_q32s((pivot - sum), fracBits);
        }
        mempool_log_barrier(2, absolute_core_id);

        if (row_id >= (j + 1)) {
            for (i = row_id; i < n; i += NUM_CORES) {
                sum = 0;
                pivot = pSrc[i * n + j];
                diag = pL[j * n + j];
                for (k = 0; k < 4 * (j >> 2U); k += 4) {
                    a0 = pL[i * n + k];
                    a1 = pL[i * n + k + 1];
                    a2 = pL[i * n + k + 2];
                    a3 = pL[i * n + k + 3];
                    b0 = pL[j * n + k];
                    b1 = pL[j * n + k + 1];
                    b2 = pL[j * n + k + 2];
                    b3 = pL[j * n + k + 3];
                    asm volatile (
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
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                }
                while (k < 2 * (j >> 1U)) {
                    a0 = pL[i * n + k];
                    a1 = pL[i * n + k + 1];
                    b0 = pL[j * n + k];
                    b1 = pL[j * n + k + 1];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pL[i * n + k];
                    b0 = pL[j * n + k];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k++;
                }
                pL[i * n + j] = FIX_DIV((pivot - sum), diag);
            }
        }
        mempool_log_barrier(2, absolute_core_id);

    }
}


void mempool_cholesky_q32p_foldleft(int32_t* pSrc,
                                    int32_t* pL,
                                    const uint32_t n,
                                    const uint32_t fracBits,
                                    const uint32_t nPE) {

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
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
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
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pL[j + k * N_BANKS];
                a1 = pL[j + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pL[j + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k++;
            }
            pL[j * N_BANKS + j] = mempool_sqrt_q32s((pivot - sum), fracBits);
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
                    asm volatile (
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
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                }
                while (k < 2 * (j >> 1U)) {
                    a0 = pL[i + k * N_BANKS];
                    a1 = pL[i + (k + 1) * N_BANKS];
                    b0 = pL[j + k * N_BANKS];
                    b1 = pL[j + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pL[i + k * N_BANKS];
                    b0 = pL[j + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k++;
                }
                pL[i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
            }
        }
        mempool_log_partial_barrier(2, absolute_core_id, nPE);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
}

void mempool_cholesky_q32p_foldright(int32_t* pSrc,
                                     int32_t* pL,
                                     const uint32_t n,
                                     const uint32_t fracBits,
                                     const uint32_t nPE) {

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
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
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
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pL[n - 1 - j + k * N_BANKS];
                a1 = pL[n - 1 - j + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pL[n - 1 - j + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k++;
            }
            pL[j * N_BANKS + n - 1 - j] = mempool_sqrt_q32s((pivot - sum), fracBits);
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
                    asm volatile (
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
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                }
                while (k < 2 * (j >> 1U)) {
                    a0 = pL[n - 1 - i + k * N_BANKS];
                    a1 = pL[n - 1 - i + (k + 1) * N_BANKS];
                    b0 = pL[n - 1 - j + k * N_BANKS];
                    b1 = pL[n - 1 - j + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pL[n - 1 - i + k * N_BANKS];
                    b0 = pL[n - 1 - j + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k++;
                }
                pL[n - 1 - i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
            }
        }
        mempool_log_partial_barrier(2, absolute_core_id, nPE);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
}


void mempool_cholesky_q32p_fold(int32_t* pSrcA,
                                int32_t* pSrcB,
                                int32_t* pLL,
                                int32_t* pLR,
                                const uint32_t n,
                                const uint32_t fracBits,
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
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
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
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pLL[j + k * N_BANKS];
                a1 = pLL[j + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pLL[j + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k++;
            }
            pLL[j * N_BANKS + j] = mempool_sqrt_q32s((pivot - sum), fracBits);
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
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
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
                    : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pLR[n - 1 - j + k * N_BANKS];
                a1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "addi %[a0],%[a0],%[h];"
                    "addi %[a1],%[a1],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "+&r" (a0), [a1] "+&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pLR[n - 1 - j + k * N_BANKS];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "addi %[a0],%[a0],%[h];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "+&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT), [h] "I" (HALF)
                    : );
                k++;
            }
            pLR[j * N_BANKS + n - 1 - j] = mempool_sqrt_q32s((pivot - sum), fracBits);
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
                    asm volatile (
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
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                }
                while (k < 2 * (j >> 1U)) {
                    a0 = pLL[i + k * N_BANKS];
                    a1 = pLL[i + (k + 1) * N_BANKS];
                    b0 = pLL[j + k * N_BANKS];
                    b1 = pLL[j + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pLL[i + k * N_BANKS];
                    b0 = pLL[j + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k++;
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
                    asm volatile (
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
                        : [a0] "+&r" (a0), [a1] "+&r" (a1), [a2] "+&r" (a2), [a3] "+&r" (a3),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1), [b2] "r" (b2), [b3] "r" (b3),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                }
                while (k < 2 * (j >> 1U)) {
                    a0 = pLR[n - 1 - i + k * N_BANKS];
                    a1 = pLR[n - 1 - i + (k + 1) * N_BANKS];
                    b0 = pLR[n - 1 - j + k * N_BANKS];
                    b1 = pLR[n - 1 - j + (k + 1) * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "mul  %[a1],%[a1],%[b1];"
                        "addi %[a0],%[a0],%[h];"
                        "addi %[a1],%[a1],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "+&r" (a0), [a1] "+&r" (a1),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0), [b1] "r" (b1),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pLR[n - 1 - i + k * N_BANKS];
                    b0 = pLR[n - 1 - j + k * N_BANKS];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "addi %[a0],%[a0],%[h];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "+&r" (a0),
                          [sum] "+&r" (sum)
                        : [b0] "r" (b0),
                          [s] "I" (FIXED_POINT), [h] "I" (HALF)
                        : );
                    k++;
                }
                pLR[n - 1 - i + j * N_BANKS] = FIX_DIV((pivot - sum), diag);
            }
        }
        mempool_log_partial_barrier(2, absolute_core_id, nPE);
    }
    mempool_log_partial_barrier(2, absolute_core_id, nPE);
}
