// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

dump(id, 1);

void mempool_cholesky_q32p(int32_t* pSrc,
                           int32_t* pL,
                           int32_t* pLT,
                           const uint32_t n,
                           const uint32_t fracBits);


void mempool_cholesky_q32p(int32_t* pSrc,
                           int32_t* pL,
                           int32_t* pLT,
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
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "srai  %[a2],%[a2],%[s];"
                    "srai  %[a3],%[a3],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    "add  %[sum],%[a2],%[sum];"
                    "add  %[sum],%[a3],%[sum];"
                    : [a0] "=&r" (a0), [a1] "=&r" (a1), [a2] "=&r" (a2), [a3] "=&r" (a3),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT)
                    : );
            }
            while (k < 2 * (j >> 1U)) {
                a0 = pL[j * n + k];
                a1 = pL[j * n + k + 1];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "mul  %[a1],%[a1],%[a1];"
                    "srai  %[a0],%[a0],%[s];"
                    "srai  %[a1],%[a1],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    "add  %[sum],%[a1],%[sum];"
                    : [a0] "=&r" (a0), [a1] "=&r" (a1),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT)
                    : );
                k += 2;
            }
            while (k < j) {
                a0 = pL[j * n + k];
                asm volatile (
                    "mul  %[a0],%[a0],%[a0];"
                    "srai  %[a0],%[a0],%[s];"
                    "add  %[sum],%[a0],%[sum];"
                    : [a0] "=&r" (a0),
                      [sum] "+&r" (sum)
                    : [s] "I" (FIXED_POINT)
                    : );
                k++;
            }
            pL[j * n + j] = mempool_sqrt_q32s((pivot - sum), fracBits);
        }
        mempool_barrier(NUM_CORES);
        //mempool_log_barrier(2, absolute_core_id);

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
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "srai  %[a2],%[a2],%[s];"
                        "srai  %[a3],%[a3],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        "add  %[sum],%[a2],%[sum];"
                        "add  %[sum],%[a3],%[sum];"
                        : [a0] "=&r" (a0), [a1] "=&r" (a1), [a2] "=&r" (a2), [a3] "=&r" (a3),
                          [b0] "=&r" (b0), [b1] "=&r" (b1), [b2] "=&r" (b2), [b3] "=&r" (b3),
                          [sum] "+&r" (sum)
                        : [s] "I" (FIXED_POINT)
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
                        "srai  %[a0],%[a0],%[s];"
                        "srai  %[a1],%[a1],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        "add  %[sum],%[a1],%[sum];"
                        : [a0] "=&r" (a0), [a1] "=&r" (a1),
                          [b0] "=&r" (b0), [b1] "=&r" (b1),
                          [sum] "+&r" (sum)
                        : [s] "I" (FIXED_POINT)
                        : );
                    k += 2;
                }
                while (k < j) {
                    a0 = pL[i * n + k];
                    b0 = pL[j * n + k];
                    asm volatile (
                        "mul  %[a0],%[a0],%[b0];"
                        "srai  %[a0],%[a0],%[s];"
                        "add  %[sum],%[a0],%[sum];"
                        : [a0] "=&r" (a0),
                          [b0] "=&r" (b0),
                          [sum] "+&r" (sum)
                        : [s] "I" (FIXED_POINT)
                        : );
                    k++;
                }
                pL[i * n + j] = FIX_DIV((pivot - sum), diag);
            }
        }
        mempool_barrier(NUM_CORES);
        // mempool_log_barrier(2, absolute_core_id);

    }
}
