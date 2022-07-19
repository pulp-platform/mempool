// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* GAUSS JORDAN INVERSION */

int mempool_GJinv_q16s(int32_t *pSrc, int32_t *pDst, uint32_t n);

int mempool_GJinv_q16s(int32_t * pSrc, int32_t * pDst, uint32_t n) {

    int32_t *pSrcT1, *pSrcT2;                    /* Temporary input data matrix pointer */
    int32_t *pDstT1, *pDstT2;                    /* Temporary output data matrix pointer */
    int32_t *pPivotRowIn;                        /* Temporary input and output data matrix pointer */
    int32_t *pPRT_in, *pPivotRowDst, *pPRT_pDst; /* Temporary input and output data matrix pointer */

    int32_t Xchg, in = 0, in1;                   /* Temporary input values  */
    uint32_t i, rowCnt, j, loopCnt, k, l;        /* loop counters */
    uint32_t flag;

    uint32_t m = n; /* M is the number of rows. However, the matirces must be square. */
    pDstT1 = pDst;  /* Working pointer for destination matrix */
    rowCnt = m;     /* Loop over the number of rows */
    flag = 0U;

    /* CREATE THE IDENTITY MATRIX */
    while (rowCnt > 0U) {
        j = m - rowCnt;
        while (j > 0U) {
            *pDstT1++ = 0;
            j--;
        }
        *pDstT1++ = 1;
        j = rowCnt - 1U;
        while (j > 0U) {
            *pDstT1++ = 0;
            j--;
        }
        rowCnt--;
    }

    /* Loop over the number of columns of the input matrix. */
    loopCnt = n;
    /* Index modifier to navigate through the columns */
    l = 0U;

    while (loopCnt > 0U) {
        /* CHECK IF PIVOT ELEMENT IS ZERO...
         * If it is zero then interchange the row with non zero row below.
         * If there is no non zero element to replace in the rows below,
         * then the matrix is Singular. */

        pSrcT1 = pSrc + (l * n);
        pDstT1 = pDst + (l * n);
        k = 1U;
        if (*pSrcT1 == 0) {
            /* Loop over the rows present below */
            for (i = (l + 1U); i < m; i++) {
                pSrcT2 = pSrcT1 + (n * i);
                pDstT2 = pDstT1 + (n * k);

                /* Check if there is a non zero pivot element to replace in the rows below */
                if (*pSrcT2 != 0) {
                    /* Exchange the row elements of the input matrix at the right of the pivot */
                    j = n - l;
                    while (j > 0U) {
                        Xchg = *pSrcT2;
                        *pSrcT2++ = *pSrcT1;
                        *pSrcT1++ = Xchg;
                        j--;
                    }
                    /* Exchange the row elements of the destination matrix */
                    j = n;
                    while (j > 0U) {
                        Xchg = *pDstT2;
                        *pDstT2++ = *pDstT1;
                        *pDstT1++ = Xchg;
                        j--;
                    }
                    flag = 1U;
                    break;
                }
                k++;
            }
        }
        /* Return when the matrix is singular */
        if ((flag == 0U) && (in == 0)) {
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
        j = (n - l);
        while (j > 0U) {
            in1 = *pSrcT1;
            *pSrcT1++ = FIX_DIV(in1, in);
            j--;
        }
        /* Loop over number of columns of the destination matrix */
        j = n;
        while (j > 0U) {
            in1 = *pSrcT2;
            *pSrcT2++ = FIX_DIV(in1, in);
            j--;
        }

        /* SUM THE MULTIPLE OF A BOTTOM ROW */
        /* Replace the rows with the sum of that row and a multiple of row i
         * so that each new element in column i above row i is zero.*/
        /* Temporary pointers for input and destination matrices */

        pSrcT1 = pSrc;
        pSrcT2 = pDst;

        i = 0U; /* pivot index */
        k = m; /* row index */
        while (k > 0U) {

            /* Only the columns to the right of the pivot are to be processed */
            if (i == l) {
                pSrcT1 += n - l;
                pSrcT2 += n;

            } else {

                /* Element of the reference row */
                in = *pSrcT1;
                /* Reference row pointers */
                pPRT_in = pPivotRowIn;
                pPRT_pDst = pPivotRowDst;

                j = (n - l); /* Replace the elements to the right of the pivot */
                while (j > 0U) {
                    in1 = *pSrcT1;
                    *pSrcT1++ = in1 - FIX_MUL(in, *pPRT_in++);
                    j--;
                }
                j = n; /* Replace the elements in the destination matrix */
                while (j > 0U) {
                    in1 = *pSrcT2;
                    *pSrcT2++ = in1 - FIX_MUL(in, *pPRT_pDst++);
                    j--;
                }
            }
            /* Increment temporary input pointer */
            pSrcT1 = pSrcT1 + l;
            /* Decrement loop counter */
            k--;
            /* Increment pivot index */
            i++;
        }

        pSrc++; /* Increment the input pointer */
        loopCnt--; /* Decrement the loop counter */
        l++; /* Increment the index modifier */
    }

//    if ((flag != 1U) && (in == 0)) {
//        for (i = 0; i < m * n; i++) {
//            if (pSrc[i] != 0)
//                break;
//        }
//        if (i == m * n)
//            return 1;
//    }

    return 0;
}
 
