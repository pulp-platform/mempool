// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* GAUSS JORDAN INVERSION */

int mempool_GJinv_q16p(int32_t * pSrc, int32_t * pDst, uint32_t n, uint32_t *flag);

int mempool_GJinv_q16p(int32_t * pSrc, int32_t * pDst, uint32_t n, uint32_t *flag) {

    int32_t *pSrcT1, *pSrcT2;                    /* Temporary input data matrix pointer */
    int32_t *pDstT1, *pDstT2;                    /* Temporary output data matrix pointer */
    int32_t *pPivotRowIn;                        /* Temporary input and output data matrix pointer */
    int32_t *pPRT_in, *pPivotRowDst, *pPRT_pDst; /* Temporary input and output data matrix pointer */

    int32_t Xchg, in = 0, in1;                    /* Temporary input values  */

    uint32_t core_id = mempool_get_core_id();
    uint32_t i, j, loopCnt, k, l;  /* loop counters */
    uint32_t m = n; /* M is the number of rows. However, the matirces must be square. */

    /* CREATE THE IDENTITY MATRIX */

    pDstT1 = pDst;  /* Working pointer for destination matrix */
    for (i = core_id; i < m; i += NUM_CORES) {
        for (j = 0; j < m; j++) {
            pDstT1[i * m + j] = (uint32_t) (i == j);
        }
    }
    mempool_barrier(NUM_CORES);

    /* Loop over the number of columns of the input matrix. */
    loopCnt = n;
    /* Index modifier to navigate through the columns */
    l = 0U;

    while (loopCnt > 0U) {

        /* CHECK IF PIVOT ELEMENT IS ZERO */

        pSrcT1 = pSrc + (l * n);
        pDstT1 = pDst + (l * n);

        in = *pSrcT1;
        k = 1U;
        /* Check if the pivot element is zero */
        if (*pSrcT1 == 0U) {

            /* Loop over the number rows present below */
            for (i = (l + 1U) + core_id; i < m; i += NUM_CORES) {
                pSrcT2 = pSrcT1 + (n * i);
                /* Check if there is element to exchange */
                //if (*flag != 0U)
                //    break;
                if (*pSrcT2 != 0U)  {
                    __atomic_fetch_add(flag, k, __ATOMIC_RELAXED);
                }
            }
            mempool_barrier(NUM_CORES);

            if (*flag != 0U) {
                pSrcT2 = pSrcT1 + (n * *flag + l);
                pDstT2 = pDstT1 + (n * *flag);
                /* Loop over number of columns
                 * to the right of the pilot element */
                for (j = core_id; j < n - l; j += NUM_CORES) {
                    /* Exchange the row elements of the input matrix */
                    Xchg = pSrcT2[j];
                    pSrcT2[j] = pSrcT1[j];
                    pSrcT1[j] = Xchg;
                }
                pSrcT1 += n - l;
                pSrcT2 += n - l;
                /* Loop over number of columns of the destination matrix */
                for(j = core_id; j < n; j += NUM_CORES) {
                    /* Exchange the row elements of the destination matrix */
                    Xchg = pDstT2[j];
                    pDstT2[j] = pDstT1[j];
                    pDstT1[j] = Xchg;
                }
                pDstT2 += n;
                pDstT1 += n;
            }
            k++;
            mempool_barrier(NUM_CORES);
        }

        /* Update the status if the matrix is singular */
        if ((*flag == 0U) && (in == 0U)) {
            return 1;
        }

        /* DIVIDE BY THE PIVOT */

        /* Points to the pivot row of input and destination matrices */
        pPivotRowIn = pSrc + (l * n);
        pPivotRowDst = pDst + (l * n);
        /* Temporary pointers to the pivot row pointers */
        pSrcT1 = pPivotRowIn;
        pSrcT2 = pPivotRowDst;
        /* Pivot element of the row */
        in = *pPivotRowIn;
        /* Loop over number of columns to the right of the pilot element */
        for(j = core_id; j < n - l; j += NUM_CORES) {
            in1 = pSrcT1[j];
            pSrcT1[j] = FIX_DIV(in1, in);
        }
        /* Loop over number of columns of the destination matrix */
        for(j = core_id; j < n; j += NUM_CORES) {
            in1 = pSrcT2[j];
            pSrcT2[j] = FIX_DIV(in1, in);
        }
        mempool_barrier(NUM_CORES);

        /*REPLACE ROWS */

        pSrcT1 = pSrc + core_id * n;
        pSrcT2 = pDst + core_id * n;
        i = core_id;
        k = m;
        for(k = core_id; k < m; k += NUM_CORES) {
            if (i != l) {
                /* Element of the reference row */
                in = *pSrcT1;
                /* Working pointers for input and destination pivot rows */
                pPRT_in = pPivotRowIn;
                pPRT_pDst = pPivotRowDst;
                /* Loop over the number of columns to the right of the pivot element,
                   to replace the elements in the input matrix */
                for (j = 0; j < n - l; j++) {
                    in1 = pSrcT1[j];
                    pSrcT1[j] = in1 - FIX_MUL(in, pPRT_in[j]);
                }
                /* Loop over the number of columns to
                   replace the elements in the destination matrix */
                for (j = 0; j < n; j++) {
                    in1 = pSrcT2[j];
                    pSrcT2[j] = in1 - FIX_MUL(in, pPRT_pDst[j]);
                }
            }
            i += NUM_CORES;
            pSrcT1 += NUM_CORES * n;
            pSrcT2 += NUM_CORES * n;
        }
        /* Increment the input pointer */
        pSrc++;
        /* Decrement the loop counter */
        loopCnt--;
        /* Increment the index modifier */
        l++;
        mempool_barrier(NUM_CORES);
    }

//    if ((flag != 1U) && (x == 0)) {
//        for (i = 0; i < m * n; i++) {
//            if (pSrc[i] != 0)
//                break;
//        }
//        if (i == m * n)
//            return 1;
//    }

    return 0;
}
