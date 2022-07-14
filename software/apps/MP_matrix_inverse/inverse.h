// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define FIXED_POINT 0
#define FIX_DIV(a,b) ((int32_t)((a << FIXED_POINT)/b))
#define FIX_MUL(a,b) ((int32_t)((a*b) >> FIXED_POINT))

dump(prova, 1);

void Transpose(int32_t *matrix, int32_t *t_matrix, int32_t n);

void MatrixMult(int32_t *matrix_1, int32_t *matrix_2, int32_t *matrix_product, int32_t n);



void getCofactor(int32_t *A, int32_t *temp, int32_t p, int32_t q, int32_t n);

int32_t determinant(int32_t *A, int32_t n);

void adjoint(int32_t *A,int32_t *adj, int32_t n);

int32_t C_inverse(int32_t *A, int32_t *inverse, int32_t n);



int GJ_inverse(int32_t *pSrc, int32_t *pDst, uint32_t n);

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

/* CRAMER MATRIX INVERSION */

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
int32_t C_inverse(int32_t *A, int32_t *inverse, int32_t n) {
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
            inverse[i * n + j]= FIX_DIV(adj[i * n + j], det);
    return 1;
}

/* GAUSS JORDAN INVERSION */

int GJ_inverse(int32_t * pSrc, int32_t * pDst, uint32_t n) {

    int32_t *pSrcT1, *pSrcT2;                    /* Temporary input data matrix pointer */
    int32_t *pDstT1, *pDstT2;                    /* Temporary output data matrix pointer */
    int32_t *pPivotRowIn;                        /* Temporary input and output data matrix pointer */
    int32_t *pPRT_in, *pPivotRowDst, *pPRT_pDst; /* Temporary input and output data matrix pointer */

    int32_t Xchg, x = 0, y;                    /* Temporary input values  */
    uint32_t i, rowCnt, flag = 0U, j, loopCnt, k, l;  /* loop counters */

    uint32_t m = n; /* M is the number of rows. However, the matirces must be square. */
    pDstT1 = pDst;  /* Working pointer for destination matrix */
    rowCnt = m;     /* Loop over the number of rows */

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
        x = *pSrcT1;
        k = 1U;
        if (x == 0) {
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
        if ((flag != 1U) && (x == 0)) {
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
        x = *pPivotRowIn;

        /* Loop over number of columns to the right of the pilot element */
        j = (n - l);
        while (j > 0U) {
            y = *pSrcT1;
            *pSrcT1++ = FIX_DIV(y, x);
            j--;
        }
        /* Loop over number of columns of the destination matrix */
        j = n;
        while (j > 0U) {
            y = *pSrcT2;
            *pSrcT2++ = FIX_DIV(y, x);
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
                x = *pSrcT1;
                /* Reference row pointers */
                pPRT_in = pPivotRowIn;
                pPRT_pDst = pPivotRowDst;

                j = (n - l); /* Replace the elements to the right of the pivot */
                while (j > 0U) {
                    y = *pSrcT1;
                    *pSrcT1++ = y - FIX_MUL(x, *pPRT_in++);
                    j--;
                }
                j = n; /* Replace the elements in the destination matrix */
                while (j > 0U) {
                    y = *pSrcT2;
                    *pSrcT2++ = y - FIX_MUL(x, *pPRT_pDst++);
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
 
