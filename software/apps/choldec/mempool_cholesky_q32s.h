// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_cholesky_q32s(int32_t* pSrc,
                           int32_t* pL,
                           int32_t* pLT,
                           const uint32_t n,
                           const uint32_t fracBits);

int32_t mempool_sqrt_q32s(int32_t Src,
                          const uint32_t fracBits);


void mempool_cholesky_q32s(int32_t* pSrc,
                           int32_t* pL,
                           int32_t* pLT,
                           const uint32_t n,
                           const uint32_t fracBits) {
    int32_t sum;
    uint32_t i, j, k;
 
    /* Loop over rows */
    for (i = 0; i < n; i++) {
        /* Loop over columns */
        for (j = 0; j <= i; j++) {

            sum = 0;
            /* Loop over the elements of row i smaller than j */
            for (k = 0; k < j; k++)
                sum += pL[i * n + k] * pL[j * n + k];
            if (j == i) {
                pL[i * n + j] = mempool_sqrt_q32s((pSrc[i * n + j] - sum), fracBits);
                pLT[j * n + i] = pL[i * n + j];
            } else {
                pL[i * n + j] = FIX_DIV((pSrc[i * n + j] - sum), pL[j * n + j]);
                pLT[j * n + i] = pL[i * n + j];
            }

        }
    }
}

int32_t mempool_sqrt_q32s(int32_t number,
                          const uint32_t fracBits) {

    int32_t res = 0;

    int32_t start = 0;
    int32_t end = 46341; // smallest integer that is larger than sqrt(0x7FFFFFFF)
    int32_t mid;
    if (number > 0) {
        while (start <= end) {
            mid = (start + end) >> 1;
            if (((mid * mid) >> fracBits) == number) {
                res = mid;
                break;
            }
            if (((mid * mid) >> fracBits) < number) {
                start = mid + 1;
                res = mid;
            } else {
                end = mid - 1;
            }
        }
    }

    return res;
}
