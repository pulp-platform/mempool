// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/**
  @brief         Cholesky decomposition with recursive Schur algorithm.
  @param[in]     
  @param[out]     
  @param[out]
  @param[in]
  @param[in]     
  @return        none
*/

void mempool_schur_q32s(int32_t* pSrc,
                        int32_t* pDst_A,
                        int32_t* pDst_B,
                        const uint32_t n,
                        const uint32_t fracBits);

/**
  @brief         Matrix triangular solver. Solves a system (A**T)X = B where A is upper triangular.
  @param[in]     pSrc_A Points to matrix A
  @param[in]     pSrc_B Points to matrix B
  @param[in]     m Number of rows of B
  @param[in]     n Number of columns of B
  @return        none
*/

void mempool_utrsv_q32s(int32_t* pSrc_A,
                        int32_t* pSrc_B,
                        const uint32_t m,
                        const uint32_t n,
                        const uint32_t fracBits);

/**
  @brief         Matrix triangular solver. Solves a system X(A**T) = B where A is lower triangular.
  @param[in]     pSrc_A Points to matrix A
  @param[in]     pSrc_B Points to matrix B
  @param[in]     m Number of rows of B
  @param[in]     n Number of columns of B
  @return        none
*/

void mempool_ltrsv_q32s(int32_t* pSrc_A,
                        int32_t* pSrc_B,
                        const uint32_t n,
                        const uint32_t m,
                        const uint32_t n,
                        const uint32_t fracBits);

/**
  @brief         Symmetric rank k operator.
  @param[in]     pSrc_A Points to matrix A
  @param[in]     pSrc_C Points to matrix C
  @param[in]     mA Number of rows of A
  @param[in]     nA Number of columns of A
  @param[in]     mC Number of rows of C
  @param[in]     nC Number of columns of C
  @return        none
*/

void mempool_syrk_q32s(int32_t* pSrc_A,
                       int32_t* pSrc_B,
                       const uint32_t mA,
                       const uint32_t nA,
                       const uint32_t mC,
                       const uint32_t nC,
                       const uint32_t fracBits);

/* 

    Computes the Cholesky factorization of a real symmetric
    positive definite matrix A using the recursive algorithm.   

    The factorization has the form
    A = U**T * U,  if UPLO = 'U', or
    A = L  * L**T,  if UPLO = 'L',
    where U is an upper triangular matrix and L is lower triangular.    

    This is the recursive version of the algorithm. It divides
    the matrix into four submatrices:   

            [  A11 | A12  ]  where A11 is n1 by n1 and A22 is n2 by n2
        A = [ -----|----- ]  with n1 = n/2
            [  A21 | A22  ]       n2 = n-n1 

    The subroutine calls itself to factor A11. Update and scale A21
    or A12, update A22 then calls itself to factor A22.

*/

void mempool_schur_q32s(int32_t* pSrc,
                        int32_t* pDst_A,
                        int32_t* pDst_B,
                        const uint32_t n,
                        const uint32_t uplo,
                        const uint32_t fracBits) {

    n1 = n / 2;
    n2 = n - n1;
    if (uplo == 1) {
        mempool_utrsv_q32s()
        mempool_syrk_q32s()
        mempool_schur_q32s()
    }

    if (uplo == 0) {
        mempool_ltrsv_q32s()
        mempool_syrk_q32s()
        mempool_schur_q32s()
    }

}

/*  @brief Matrix triangular solver. 
    Solves a system (A**T)X = B where A is upper triangular. */

void mempool_utrsv_q32s(int32_t* pSrc_A,
                        int32_t* pSrc_B,
                        const uint32_t m,
                        const uint32_t n,
                        const uint32_t fracBits) {

    for (j = 0; j < n; j++) {
        for (i = 0; k < m; k++) {

            temp = pSrc_B[i * m + j];
            for (k = 0; k < i - 1; k++) {
                temp = temp - pSrc_A[k * n + i] * pSrcB[k * m + j];
            }
            pSrc_B = temp / p_SrcA[i * m + i];

        } 
    }
    return;

}

/* @brief Matrix triangular solver. 
   Solves a system X(A**T) = B where A is lower triangular. */

void mempool_ltrsv_q32s(int32_t* pSrc_A,
                        int32_t* pSrc_B,
                        const uint32_t m,
                        const uint32_t n,
                        const uint32_t fracBits) {

    for (k = 0; k < n; k++) {

        temp = 1 / (pSrc_A[k * n + k]);
        for (i = 0; i < m; i++) {
            pSrc_B[i * m + k] = temp * pSrc_B[i * m + k];
        }
        for (j = k; j < n; j++) {
            if (pSrc_A[j * n + k] != 0) {
                temp = pSrc_A[j * n + k];
                for (i = 0; i < m; i++) {
                    pSrc_B[i * m + j] = pSrc_B[i * m + j] - temp * pSrc_B[i * m + k];
                }
            }
        }

    }
}

/**
  @brief         Symmetric rank k operator.
  @param[in]     pSrc_A Points to matrix A
  @param[in]     pSrc_C Points to matrix C
  @param[in]     mA Number of rows of A
  @param[in]     nA Number of columns of A
  @param[in]     mC Number of rows of C
  @param[in]     nC Number of columns of C
  @return        none
*/

void mempool_syrk_q32s(int32_t* pSrc_A,
                       int32_t* pSrc_B,
                       const uint32_t mA,
                       const uint32_t nA,
                       const uint32_t mC,
                       const uint32_t nC,
                       const uint32_t fracBits) {



}
   