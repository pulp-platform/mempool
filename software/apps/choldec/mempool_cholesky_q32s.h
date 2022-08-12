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
    int32_t sum, result;
    uint32_t i, j, k, l;
    int32_t a0, a1, a2, a3;
    int32_t b0, b1, b2, b3;
    int32_t pivot, diag;
 
    /* Loop over rows */
    for (i = 0; i < n; i++) {
        /* Loop over columns */
        for (j = 0; j <= i; j++) {

            pivot = pSrc[i * n + j];
            diag = pL[j * n + j];

            sum = 0;
            l = j - 1;
            if (j > 0) {
                /* Loop over the elements of row i smaller than j */
                for (k = 0; k < 4 * (l >> 2U); k += 4) {
                    a0 = pL[i * n + k];
                    a1 = pL[i * n + k + 1];
                    a2 = pL[i * n + k + 2];
                    a3 = pL[i * n + k + 3];
                    b0 = pL[j * n + k];
                    b1 = pL[j * n + k + 1];
                    b2 = pL[j * n + k + 2];
                    b3 = pL[j * n + k + 3];
                    a0 = a0 * b0;
                    a1 = a1 * b1;
                    a2 = a2 * b2;
                    a3 = a3 * b3;
                    a0 = a0 >> FIXED_POINT;
                    a1 = a1 >> FIXED_POINT;
                    a2 = a2 >> FIXED_POINT;
                    a3 = a3 >> FIXED_POINT;
                    sum += a0;
                    sum += a1;
                    sum += a2;
                    sum += a3;
                }
                while (k < 2 * (l >> 1U)) {
                    a0 = pL[i * n + k];
                    a1 = pL[j * n + k + 1];
                    b0 = pL[j * n + k];
                    b1 = pL[j * n + k + 1];
                    a0 = a0 * b0;
                    a1 = a1 * b1;
                    a0 = a0 >> FIXED_POINT;
                    a1 = a1 >> FIXED_POINT;
                    sum += a0;
                    sum += a1;
                    k += 2;
                }
                while (k < l) {
                    a0 = pL[i * n + k];
                    b0 = pL[j * n + k];
                    a0 = a0 * b0;
                    a0 = a0 >> FIXED_POINT;
                    sum += a0;
                    k++;
                }
                b0 = pL[j * n + k];
                a0 = result * b0;
                a0 = a0 >> FIXED_POINT;
                sum += a0;
                pL[i * n + l] = result;
//                // Transpose
//                pLT[l * n + i] = result;
            }
            if (j != i) {
                result = FIX_DIV((pivot - sum), diag);
            }

        }
        pL[i * n + j] = mempool_sqrt_q32s((pivot - sum), fracBits);
//        // Transpose
//        pLT[j * n + i] = result;
    }
}

int32_t mempool_sqrt_q32s(int32_t number,
                          const uint32_t fracBits) {

    int32_t res = 0;

    int32_t start = 0;
    int32_t end = 46341; // smallest integer that is larger than sqrt(0x7FFFFFFF)
    int32_t mid, mid2;

//    int32_t m1, m2, tmp, i;
//    m1 = (end - start) >> 1U;
//    m2 = m1 * m1;

    if (number > 0) {

        mid = (start + end) >> 1;
        mid2 = mid * mid;
        while (start <= end) {
            if ((mid2 >> fracBits) == number) {
                res = mid;
                break;
            }
            if ((mid2 >> fracBits) < number) {
                start = mid + 1;
                res = mid;
                mid = (start + end) >> 1;
                mid2 = mid * mid;
            } else {
                end = mid - 1;
                mid = (start + end) >> 1;
                mid2 = mid * mid;
            }
        }

//        i = 0;
//        while (i < 5) {
//            if ((m2 >> fracBits) == number) {
//                res = m1;
//                break;
//            }
//            if ((m2 >> fracBits) < number) {
//                m2 = m2 >> 2U;
//                m1 = m1 >> 1U;
//            } else {
//                tmp = (m2 >> 2U);
//                m2 = (tmp << 3U) + tmp;
//                m1 = m1 + (m1 >> 1U);
//            }
//            i++;
//        }
    }

    return res;
}
