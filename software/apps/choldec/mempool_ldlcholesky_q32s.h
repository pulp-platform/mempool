// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the ApSrcche License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich


/**
   * @brief Floating-point LDL^t decomposition of positive semi-definite matrix.
   * @param[in]  pSrc   points to the instance of the input floating-point matrix structure.
   * @param[out] pDst   points to the instance of the output floating-point triangular matrix structure.
   * @param[out] pDiag   points to the instance of the output floating-point diagonal matrix structure.
   * @param[out] pPerm   points to the instance of the output floating-point permutation vector.
   * @return The function returns ARM_MATH_SIZE_MISMATCH, if the dimensions do not match.
   * @return     none
   * @par
   *  Computes the LDL^t decomposition of a matrix A such that P A P^t = L D L^t.
   */
void mempool_ldlcholesky_q32s(int32_t * pSrc,
                              int32_t * pDst,
                              int32_t * pDiag,
                              uint32_t n,
                              uint32_t * pPerm) {

    int32_t fullRank = 1;
    uint32_t i, j, k;
    uint32_t idxPivot = 0, diag;

    int32_t pivot;
    int32_t tmp0, tmp1, tmp2, tmp3;
    int32_t a, b0, b1, b2, b3;

    pDst = pSrc;
    for (k = 0; k < n; k += 4) {
        pPerm[k] = k;
        pPerm[k + 1] = k + 1;
        pPerm[k + 2] = k + 2;
        pPerm[k + 3] = k + 3;
    }

    // Loop over rows
    for(k = 0; k < n; k++) {

        /* Find pivot, the largest element on the main diagonal */
        pivot = (int32_t) 0xFFFFFFFF;
        idxPivot = k;
        for (i = k; i < n; i++) {
            if (pSrc[i * n + i] > pivot) {
                pivot = pSrc[i * n + i];
                idxPivot = i;
            }
        }
        if(idxPivot != k) {
            /* Exchange current row with pivot row */
            for (j = 0; j < n; j += 4) {
                tmp0 = pSrc[k * n + j];
                tmp1 = pSrc[k * n + j + 1];
                tmp2 = pSrc[k * n + j + 2];
                tmp3 = pSrc[k * n + j + 3];
                b0 = pSrc[idxPivot * n + j];
                b1 = pSrc[idxPivot * n + j + 1];
                b2 = pSrc[idxPivot * n + j + 2];
                b3 = pSrc[idxPivot * n + j + 3];
                pSrc[k * n + j] = b0;
                pSrc[k * n + j + 1] = b1;
                pSrc[k * n + j + 2] = b2;
                pSrc[k * n + j + 3] = b3;
                pSrc[idxPivot * n + j] = tmp0;
                pSrc[idxPivot * n + j + 1] = tmp1;
                pSrc[idxPivot * n + j + 2] = tmp2;
                pSrc[idxPivot * n + j + 3] = tmp3;

            }
            /* Exchange current column with pivot column */
            for (i = 0; i < n; i += 4) {
                tmp0 = pSrc[i * n + k];
                tmp1 = pSrc[(i + 1) * n + k];
                tmp2 = pSrc[(i + 2) * n + k];
                tmp3 = pSrc[(i + 3) * n + k];
                pSrc[i * n + k] = pSrc[i * n + idxPivot];
                pSrc[(i + 1) * n + k] = pSrc[(i + 1) * n + idxPivot];
                pSrc[(i + 2) * n + k] = pSrc[(i + 2) * n + idxPivot];
                pSrc[(i + 3) * n + k] = pSrc[(i + 3) * n + idxPivot];
                pSrc[i * n + idxPivot] = tmp0;
                pSrc[(i + 1) * n + idxPivot] = tmp1;
                pSrc[(i + 2) * n + idxPivot] = tmp2;
                pSrc[(i + 3) * n + idxPivot] = tmp3;
            }
        }
        pPerm[k] = idxPivot;
        if (ABS(pivot) == 0) {
            fullRank = 0;
            break;
        }

        /* Subtract (A_ik * A_jk) / pivot */
        for (i = k + 1; i < n; i++) {
            for (j = k + 1; j < 4 * (n >> 2U); j += 4) {
                a = pSrc[i * n + k];
                b0 = pSrc[j * n + k];
                b1 = pSrc[(j + 1) * n + k];
                b2 = pSrc[(j + 2) * n + k];
                b3 = pSrc[(j + 3) * n + k];
                tmp0 = FIX_MUL(a, b0);
                tmp1 = FIX_MUL(a, b1);
                tmp2 = FIX_MUL(a, b2);
                tmp3 = FIX_MUL(a, b3);
                tmp0 = FIX_DIV(tmp0, pivot);
                tmp1 = FIX_DIV(tmp1, pivot);
                tmp2 = FIX_DIV(tmp2, pivot);
                tmp3 = FIX_DIV(tmp3, pivot);
                pSrc[i * n + j] = pSrc[i * n + j] - tmp0;
                pSrc[i * n + j + 1] = pSrc[i * n + j + 1] - tmp1;
                pSrc[i * n + j + 2] = pSrc[i * n + j + 2] - tmp2;
                pSrc[i * n + j + 3] = pSrc[i * n + j + 3] - tmp3;
            }
            while (j < 2 * (n >> 1U)) {
                a = pSrc[i * n + k];
                b0 = pSrc[j * n + k];
                b1 = pSrc[(j + 1) * n + k];
                tmp0 = FIX_MUL(a, b0);
                tmp1 = FIX_MUL(a, b1);
                tmp0 = FIX_DIV(tmp0, pivot);
                tmp1 = FIX_DIV(tmp1, pivot);
                pSrc[i * n + j + 1] = pSrc[i * n + j + 1] - tmp0;
                pSrc[i * n + j + 2] = pSrc[i * n + j + 2] - tmp0;
                j += 2;
            }
            while (j < n) {
               a = pSrc[i * n + k];
               b0 = pSrc[j * n + k];
               tmp0 = FIX_MUL(a, b0);
               tmp0 = FIX_DIV(tmp0, pivot);
               pSrc[i * n + j + 1] = pSrc[i * n + j + 1] - tmp0;
               j++;
            }
        }

        /* Divide elements on the pivot column by the pivot */
        for (i = k + 1; i < 4 * (n >> 2U); i += 4) {
            pSrc[i * n + k] = pSrc[i * n + k] / pivot;
            pSrc[(i + 1) * n + k] = pSrc[(i + 1) * n + k] / pivot;
            pSrc[(i + 2) * n + k] = pSrc[(i + 2) * n + k] / pivot;
            pSrc[(i + 3) * n + k] = pSrc[(i + 3) * n + k] / pivot;
        }
        while (i < 2 * (i >> 2U)) {
            pSrc[i * n + k] = pSrc[i * n + k] / pivot;
            pSrc[(i + 1) * n + k] = pSrc[(i + 1) * n + k] / pivot;
        }
        while (i < n) {
            pSrc[i * n + k] = pSrc[i * n + k] / pivot;
            i++;
        }
    }

    diag = idxPivot;
    if (!fullRank) {
        diag--;
        for(i = 0; i < n; i += 4) {
            for (j = idxPivot; j < n; j++) {
                pDst[i * n + j] = 0;
                pDst[(i + 1) * n + j] = 0;
                pDst[(i + 2) * n + j] = 0;
                pDst[(i + 3) * n + j] = 0;
            }
        }
    }
    for (i = 0; i < n; i += 4) {
        for (j = i + 1; j < n; j++) {
            pDst[i * n + j] = 0;
            pDst[(i + 1) * n + j] = 0;
            pDst[(i + 2) * n + j] = 0;
            pDst[(i + 3) * n + j] = 0;
        }
    }
    for (k = 0; k < diag; k += 4) {
        tmp0 = pDst[k * n + k];
        tmp1 = pDst[(k + 1) * n + k + 1];
        tmp2 = pDst[(k + 2) * n + k + 2];
        tmp3 = pDst[(k + 3) * n + k + 3];
        pDiag[k * n + k] = tmp0;
        pDiag[(k + 1) * n + k + 1] = tmp1;
        pDiag[(k + 2) * n + k + 2] = tmp2;
        pDiag[(k + 3) * n + k + 3] = tmp3;
        pDst[k * n + k] = 1;
        pDst[(k + 1) * n + k + 1] = 1;
        pDst[(k + 2) * n + k + 2] = 1;
        pDst[(k + 3) * n + k + 3] = 1;
    }

}
