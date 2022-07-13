// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void Transpose(int32_t *matrix, int32_t *t_matrix, int32_t n);

void MatrixMult(int32_t *matrix_1, int32_t *matrix_2, int32_t *matrix_product, int32_t n);

void getCofactor(int32_t *A, int32_t *temp, int32_t p, int32_t q, int32_t n);

int32_t determinant(int32_t *A, int32_t n);

void adjoint(int32_t *A,int32_t *adj, int32_t n);

int32_t inverse(int32_t *A, int32_t *inverse, int32_t n);

int plp_mat_inv_f32s_xpulpv2(int32_t *__restrict__ pSrc, int32_t *__restrict__ pDst, uint32_t n);

 
void Transpose(int32_t *matrix, int32_t *t_matrix, int32_t n) {
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {
             t_matrix[j * n + i]=matrix[i * n + j];
        }
    }
}
 
void MatrixMult(int32_t *matrix_1, int32_t *matrix_2, int32_t *matrix_product, int32_t n) {
    int k;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < n; j++) {             // not j<M
            matrix_product[i * n + j] = 0;
            for (k = 0; k < n; k++) {
                matrix_product[i * n + j] += matrix_1[i * n + k] * matrix_2[k * n + j];
            }
        }
    }
}

// Function to get cofactor
void getCofactor(int32_t *A, int32_t *temp, int32_t p, int32_t q, int32_t n) {
    int32_t i = 0, j = 0;
    // Looping for each element of the matrix
    for (int32_t row = 0; row < n; row++) {
      for (int32_t col = 0; col < n; col++) {
        // Copying into temporary matrix only those element
        // which are not in given row and column
        if (row != p && col != q) {
          temp[i * N + j++] = A[row * N + col];
          // Row is filled, so increase row index and
          // reset col index
          if (j == n - 1) {
              j = 0;
              i++;
          }
        }
      }
    }
}
 
// Recursive function for finding determinant of matrix.
int32_t determinant(int32_t *A, int32_t n) {

    int32_t D = 0; // Initialize result
    // Base case : if matrix contains single element
    if (n == 1)
        return A[0];
 
    int32_t temp[N * N]; // To store cofactors
    for(int32_t i =0; i < N*N; i++)
      temp[i] = 0;

    int32_t sign = 1; // To store sign multiplier
    // Iterate for each element of first row
    for (int32_t f = 0; f < n; f++) {

        // Getting Cofactor of A[0][f]
        getCofactor(A, temp, 0, f, n);

        D += sign * A[0 * N + f] * determinant(temp, n - 1);
        // terms are to be added with alternate sign
        sign = -sign;
    }

    return D;
}
 
// Function to get adjoint
void adjoint(int32_t *A,int32_t *adj, int32_t n) {
    if (n == 1) {
        adj[0] = 1;
        return;
    }
    // temp is used to store cofactors 
    int32_t sign = 1;
    int32_t temp[N * N];
    for (int32_t i = 0; i < N; i++) {
        for (int32_t j = 0; j < N; j++) {
            // Get cofactor
            getCofactor(A, temp, i, j, N);
            // sign of adj positive if sum of row
            // and column indexes is even.
            sign = ((i + j) % 2 == 0) ? 1 : -1;
            // Interchanging rows and columns to get the
            // transpose of the cofactor matrix
            adj[j * N + i] = (sign)*(determinant(temp, N - 1));
        }
    }
}
 
// Function to calculate and store inverse, returns false if
// matrix is singular
int32_t inverse(int32_t *A, int32_t *inverse, int32_t n) {
    // Find determinant of A[][]
    int32_t det = determinant(A, n);
    if (det == 0) {
        printf("Singular matrix, can't find its inverse\n");
        return 0;
    }
 
    // Find adjoint
    int32_t adj[n * n];
    adjoint(A, adj, n);
 
    // Find Inverse using formula "inverse(A) = adj(A)/det(A)"
    for (int32_t i = 0; i < n; i++)
        for (int32_t j = 0; j < n; j++)
            inverse[i * n + j]= adj[i * n + j] / det;
    return 1;
}


int plp_mat_inv_f32s_xpulpv2(int32_t *__restrict__ pSrc, int32_t *__restrict__ pDst, uint32_t n) {

    int32_t *pSrcT1, *pSrcT2;                    /* Temporary input data matrix pointer */
    int32_t *pDstT1, *pDstT2;                    /* Temporary output data matrix pointer */
    int32_t *pPivotRowIn;                        /* Temporary input and output data matrix pointer */
    int32_t *pPRT_in, *pPivotRowDst, *pPRT_pDst; /* Temporary input and output data matrix pointer */

    int32_t Xchg, in = 0, in1;                      /* Temporary input values  */
    uint32_t i, rowCnt, flag = 0U, j, loopCnt, k, l; /* loop counters */

    uint32_t m = n; /* M is the number of rows. However, the matirces must be square. */

    /* Working pointer for destination matrix */
    pDstT1 = pDst;

    /* Loop over the number of rows */
    rowCnt = m;

    /* Making the destination matrix as identity matrix */
    while (rowCnt > 0U) {
        /* Writing all zeroes in lower triangle of the destination matrix */
        j = m - rowCnt;
        while (j > 0U) {
            *pDstT1++ = 0;
            j--;
        }

        /* Writing all ones in the diagonal of the destination matrix */
        *pDstT1++ = 1;

        /* Writing all zeroes in upper triangle of the destination matrix */
        j = rowCnt - 1U;
        while (j > 0U) {
            *pDstT1++ = 0;
            j--;
        }

        /* Decrement loop counter */
        rowCnt--;
    }

    /* Loop over the number of columns of the input matrix.
       All the elements in each column are processed by the row operations */
    loopCnt = n;

    /* Index modifier to navigate through the columns */
    l = 0U;

    while (loopCnt > 0U) {
        /* Check if the pivot element is zero..
         * If it is zero then interchange the row with non zero row below.
         * If there is no non zero element to replace in the rows below,
         * then the matrix is Singular. */

        /* Working pointer for the input matrix that points
         * to the pivot element of the particular row  */
        pSrcT1 = pSrc + (l * n);

        /* Working pointer for the destination matrix that points
         * to the pivot element of the particular row  */
        pDstT1 = pDst + (l * n);

        /* Temporary variable to hold the pivot value */
        in = *pSrcT1;

        /* Destination pointer modifier */
        k = 1U;

        /* Check if the pivot element is zero */
        if (*pSrcT1 == 0) {
            /* Loop over the number rows present below */

            for (i = (l + 1U); i < m; i++) {
                /* Update the input and destination pointers */
                pSrcT2 = pSrcT1 + (n * i);
                pDstT2 = pDstT1 + (n * k);

                /* Check if there is a non zero pivot element to
                 * replace in the rows below */
                if (*pSrcT2 != 0) {
                    /* Loop over number of columns
                     * to the right of the pilot element */
                    j = n - l;

                    while (j > 0U) {
                        /* Exchange the row elements of the input matrix */
                        Xchg = *pSrcT2;
                        *pSrcT2++ = *pSrcT1;
                        *pSrcT1++ = Xchg;

                        /* Decrement the loop counter */
                        j--;
                    }

                    /* Loop over number of columns of the destination matrix */
                    j = n;

                    while (j > 0U) {
                        /* Exchange the row elements of the destination matrix */
                        Xchg = *pDstT2;
                        *pDstT2++ = *pDstT1;
                        *pDstT1++ = Xchg;

                        /* Decrement loop counter */
                        j--;
                    }

                    /* Flag to indicate whether exchange is done or not */
                    flag = 1U;

                    /* Break after exchange is done */
                    break;
                }

                /* Update the destination pointer modifier */
                k++;

                /* Decrement loop counter */
            }
        }

        /* Update the status if the matrix is singular */
        if ((flag != 1U) && (in == 0)) {
            return 1;
        }

        /* Points to the pivot row of input and destination matrices */
        pPivotRowIn = pSrc + (l * n);
        pPivotRowDst = pDst + (l * n);

        /* Temporary pointers to the pivot row pointers */
        pSrcT1 = pPivotRowIn;
        pSrcT2 = pPivotRowDst;

        /* Pivot element of the row */
        in = *pPivotRowIn;

        /* Loop over number of columns
         * to the right of the pilot element */
        j = (n - l);

        while (j > 0U) {
            /* Divide each element of the row of the input matrix
             * by the pivot element */
            in1 = *pSrcT1;
            *pSrcT1++ = in1 / in;

            /* Decrement the loop counter */
            j--;
        }

        /* Loop over number of columns of the destination matrix */
        j = n;

        while (j > 0U) {
            /* Divide each element of the row of the destination matrix
             * by the pivot element */
            in1 = *pSrcT2;
            *pSrcT2++ = in1 / in;

            /* Decrement the loop counter */
            j--;
        }

        /* Replace the rows with the sum of that row and a multiple of row i
         * so that each new element in column i above row i is zero.*/

        /* Temporary pointers for input and destination matrices */
        pSrcT1 = pSrc;
        pSrcT2 = pDst;

        /* index used to check for pivot element */
        i = 0U;

        /* Loop over number of rows */
        /*  to be replaced by the sum of that row and a multiple of row i */
        k = m;

        while (k > 0U) {
            /* Check for the pivot element */
            if (i == l) {
                /* If the processing element is the pivot element,
                   only the columns to the right are to be processed */
                pSrcT1 += n - l;

                pSrcT2 += n;
            } else {
                /* Element of the reference row */
                in = *pSrcT1;

                /* Working pointers for input and destination pivot rows */
                pPRT_in = pPivotRowIn;
                pPRT_pDst = pPivotRowDst;

                /* Loop over the number of columns to the right of the pivot element,
                   to replace the elements in the input matrix */
                j = (n - l);

                while (j > 0U) {
                    /* Replace the element by the sum of that row
                       and a multiple of the reference row  */
                    in1 = *pSrcT1;
                    *pSrcT1++ = in1 - (in * *pPRT_in++);

                    /* Decrement the loop counter */
                    j--;
                }

                /* Loop over the number of columns to
                   replace the elements in the destination matrix */
                j = n;

                while (j > 0U) {
                    /* Replace the element by the sum of that row
                       and a multiple of the reference row  */
                    in1 = *pSrcT2;
                    *pSrcT2++ = in1 - (in * *pPRT_pDst++);

                    /* Decrement loop counter */
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

        /* Increment the input pointer */
        pSrc++;

        /* Decrement the loop counter */
        loopCnt--;

        /* Increment the index modifier */
        l++;
    }

    if ((flag != 1U) && (in == 0)) {
        for (i = 0; i < m * n; i++) {
            if (pSrc[i] != 0)
                break;
        }

        if (i == m * n)
            return 1;
    }

    return 0;
}
 
