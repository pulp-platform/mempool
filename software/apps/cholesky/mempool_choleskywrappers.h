// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* Cholesky decomposition */

void mempool_cholesky_q32p_fldL(int32_t *pSrc, int32_t *pL, const uint32_t n,
                                const uint32_t nPE);

void mempool_cholesky_q32p_fldR(int32_t *pSrc, int32_t *pL, const uint32_t n,
                                const uint32_t nPE);

void mempool_cholesky_q32p_fld(int32_t *pSrcA, int32_t *pSrcB, int32_t *pLL,
                               int32_t *pLR, const uint32_t n,
                               const uint32_t nPE);

void mempool_cholesky_q32p_fld_scheduler(int32_t *pSrcA, int32_t *pSrcB,
                                         int32_t *pLL, int32_t *pLR,
                                         const uint32_t n, const uint32_t n_row,
                                         const uint32_t n_col);

/* Solution of linear systems based on Cholesky decomposition */

void mempool_linearsolver_q32s_scheduler(int32_t *pSrc, int32_t *pL,
                                         int32_t *pIn, const uint32_t n_itr);

void mempool_linearsolver_q32s_fld_scheduler(int32_t *pSrc, int32_t *pL,
                                             int32_t *pIn, const uint32_t n,
                                             const uint32_t n_row,
                                             const uint32_t n_col);

void mempool_linearsolver_q32p_fld(int32_t *pSrcA, int32_t *pSrcB, int32_t *pLL,
                                   int32_t *pLR, int32_t *pInA, int32_t *pInB,
                                   const uint32_t n, const uint32_t nPE);

void mempool_linearsolver_q32p_fld_scheduler(int32_t *pSrcA, int32_t *pSrcB,
                                             int32_t *pLL, int32_t *pLR,
                                             int32_t *pIn, const uint32_t n,
                                             const uint32_t n_row,
                                             const uint32_t n_col);

/**
  @brief         Multiple iterations of the Cholesky decomposition
  @param[in]     pSrc points to input matrix
  @param[in/out] pL points to lower triangular matrix LEFT-FOLDED
  @param[in/out] pIn points to input vector
  @param[in]     n system dimension
  @param[in]     nPE number of processing elements
  @return        none
*/
void mempool_cholesky_q32p_fldL(int32_t *pSrc, int32_t *pL, const uint32_t n,
                                const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t j;
  for (j = 0; j < n; j++) {
    mempool_cholesky_q32p_FLsqrtsum_fld(pSrc, pL, core_id, j);
    mempool_log_partial_barrier(2, core_id, nPE);
    mempool_cholesky_q32p_FLdivisum_fld(pSrc, pL, core_id, n, j);
    mempool_log_partial_barrier(2, core_id, nPE);
  }
  return;
}

/**
  @brief         Multiple iterations of the Cholesky decomposition
  @param[in]     pSrc points to input matrix
  @param[in/out] pL points to lower triangular matrix LEFT-FOLDED
  @param[in/out] pIn points to input vector
  @param[in]     n system dimension
  @param[in]     nPE number of processing elements
  @return        none
*/
void mempool_cholesky_q32p_fldR(int32_t *pSrc, int32_t *pL, const uint32_t n,
                                const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t j;
  for (j = 0; j < n; j++) {
    mempool_cholesky_q32p_FRsqrtsum_fld(pSrc, pL, core_id, n, j);
    mempool_log_partial_barrier(2, core_id, nPE);
    mempool_cholesky_q32p_FRdivisum_fld(pSrc, pL, core_id, n, j);
    mempool_log_partial_barrier(2, core_id, nPE);
  }
  return;
}

/**
  @brief         Multiple iterations of the Cholesky decomposition
  @param[in]     pSrcA points to input matrix
  @param[in]     pSrcB points to input matrix
  @param[in/out] pLL points to lower triangular matrix LEFT-FOLDED
  @param[in/out] pLR points to lower triangular matrix RIGHT-FOLDED
  @param[in/out] pIn points to input vector
  @param[in]     n system dimension
  @param[in]     nPE number of processing elements
  @return        none
*/
void mempool_cholesky_q32p_fld(int32_t *pSrcA, int32_t *pSrcB, int32_t *pLL,
                               int32_t *pLR, const uint32_t n,
                               const uint32_t nPE) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t j;
  for (j = 0; j < n; j++) {
    mempool_cholesky_q32p_FLsqrtsum_fld(pSrcA, pLL, core_id, j);
    mempool_cholesky_q32p_FRsqrtsum_fld(pSrcB, pLR, core_id, n, j);
    mempool_log_partial_barrier(2, core_id, nPE);
    mempool_cholesky_q32p_FLdivisum_fld(pSrcA, pLL, core_id, n, j);
    mempool_cholesky_q32p_FRdivisum_fld(pSrcB, pLR, core_id, n, j);
    mempool_log_partial_barrier(2, core_id, nPE);
  }
  return;
}

/**
  @brief         Multiple iterations of the Cholesky decomposition
  @param[in]     pSrcA points to input matrix
  @param[in]     pSrcB points to input matrix
  @param[in/out] pLL points to lower triangular matrix LEFT-FOLDED
  @param[in/out] pLL points to lower triangular matrix RIGHT-FOLDED
  @param[in/out] pIn points to input vector
  @param[in]     n system dimension
  @param[in]     n_row number of algorithms executed sequentially by the same
  subset of cores
  @param[in]     n_col number of parallel instances over different subsets of
  cores of the cluster
  @return        none
*/
void mempool_cholesky_q32p_fld_scheduler(int32_t *pSrcA, int32_t *pSrcB,
                                         int32_t *pLL, int32_t *pLR,
                                         const uint32_t n, const uint32_t n_row,
                                         const uint32_t n_col) {

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t column_id = absolute_core_id / (n >> 2U);
  uint32_t core_id = absolute_core_id % (n >> 2U);
  uint32_t idx_row, idx_col;
  uint32_t j;

  for (j = 0; j < n; j++) {
    for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
      for (idx_row = 0; idx_row < n_row; idx_row++) {
        mempool_cholesky_q32p_FLsqrtsum_fld(
            pSrcA + column_id * n, pLL + idx_col * n + idx_row * (n * N_BANKS),
            core_id, j);
        mempool_cholesky_q32p_FRsqrtsum_fld(
            pSrcB + column_id * n, pLR + idx_col * n + idx_row * (n * N_BANKS),
            core_id, n, j);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
    for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
      for (idx_row = 0; idx_row < n_row; idx_row++) {
        mempool_cholesky_q32p_FLdivisum_fld(
            pSrcA + column_id * n, pLL + idx_col * n + idx_row * (n * N_BANKS),
            core_id, n, j);
        mempool_cholesky_q32p_FRdivisum_fld(
            pSrcB + column_id * n, pLR + idx_col * n + idx_row * (n * N_BANKS),
            core_id, n, j);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
  }
  return;
}

/**
  @brief         Multiple iterations of the linear system solver
  @param[in]     pSrc points to input matrix
  @param[in/out] pL points to lower triangular matrix
  @param[in/out] pIn points to input vector b
  @param[in]     n system dimentsion
  @param[in]     n_itr number of iterations
  @return        none
*/
void mempool_linearsolver_q32s_scheduler(int32_t *pSrc, int32_t *pL,
                                         int32_t *pIn, const uint32_t n_itr) {
  uint32_t itr;
  for (itr = 0; itr < n_itr; itr++) {
    mempool_linearsolver_q32s(pSrc, pL, pIn, N);
    mempool_uprtrisolver_q32s(pL, pIn, N);
  }
  return;
}

/**
  @brief         Multiple iterations of a single-core linear system solver
  @param[in]     pSrc points to input matrix
  @param[in/out] pL points to lower triangular matrix
  @param[in/out] pIn points to input vector b
  @param[in]     n system dimension
  @param[in]     n_row number of algorithms executed sequentially by the same
  core
  @param[in]     n_col number of parallel instances over different cores of the
  cluster
  @return        none
*/
void mempool_linearsolver_q32s_fld_scheduler(int32_t *pSrc, int32_t *pL,
                                             int32_t *pIn, const uint32_t n,
                                             const uint32_t n_row,
                                             const uint32_t n_col) {
  uint32_t core_id = mempool_get_core_id();
  uint32_t idx_row, idx_col = core_id;
  for (idx_row = 0; idx_row < n_row; idx_row++) {
    mempool_linearsolver_q32s_fld(pSrc + idx_col * n,
                                  pL + idx_col * n + idx_row * N_BANKS,
                                  pIn + idx_col * n, n);
    mempool_uprtrisolver_q32s_fld(pL + idx_col * n + idx_row * N_BANKS,
                                  pIn + idx_col * n, n);
  }
  if (idx_col > 1)
    mempool_log_partial_barrier(2, core_id, n_col * (n >> 2U));
  return;
}

/**
  @brief         Multiple iterations of the linear system solver
  @param[in]     pSrcA points to input matrix
  @param[in]     pSrcB points to input matrix
  @param[in/out] pLL points to lower triangular matrix LEFT-FOLDED
  @param[in/out] pLL points to lower triangular matrix RIGHT-FOLDED
  @param[in/out] pIn points to input vector
  @param[in]     n system dimension
  @param[in]     n_row number of algorithms executed sequentially by the same
  subset of cores
  @param[in]     n_col number of parallel instances over different subsets of
  cores of the cluster
  @return        none
*/
void mempool_linearsolver_q32p_fld_scheduler(int32_t *pSrcA, int32_t *pSrcB,
                                             int32_t *pLL, int32_t *pLR,
                                             int32_t *pIn, const uint32_t n,
                                             const uint32_t n_row,
                                             const uint32_t n_col) {

  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t column_id = absolute_core_id / (n >> 2U);
  uint32_t core_id = absolute_core_id % (n >> 2U);
  uint32_t idx_row, idx_col;
  uint32_t j;

  for (j = 0; j < n; j++) {
    for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
      for (idx_row = 0; idx_row < n_row; idx_row++) {
        mempool_linearsolver_q32p_FLsqrtsum_fld(
            pSrcA + idx_col * n, pLL + idx_col * n + idx_row * (n * N_BANKS),
            pIn + idx_col * n, core_id, j);
        mempool_linearsolver_q32p_FRsqrtsum_fld(
            pSrcB + idx_col * n, pLR + idx_col * n + idx_row * (n * N_BANKS),
            pIn + idx_col * n, core_id, n, j);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
    for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
      for (idx_row = 0; idx_row < n_row; idx_row++) {
        mempool_linearsolver_q32p_FLdivisum_fld(
            pSrcA + idx_col * n, pLL + idx_col * n + idx_row * (n * N_BANKS),
            pIn + idx_col * n + idx_row * N_BANKS, core_id, n, j);
        mempool_linearsolver_q32p_FRdivisum_fld(
            pSrcB + idx_col * n, pLR + idx_col * n + idx_row * (n * N_BANKS),
            pIn + idx_col * n, core_id, n, j);
      }
    }
    mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
  }

  for (idx_col = column_id; idx_col < n_col; idx_col += n_col) {
    for (idx_row = 0; idx_row < n_row; idx_row++) {
      mempool_linearsolver_q32p_trisolverL_fld(
          pLL + idx_col * n + idx_row * (n * N_BANKS), pIn + idx_col * n,
          core_id, n_col * (n >> 2U));
      mempool_linearsolver_q32p_trisolverR_fld(
          pLR + idx_col * n + idx_row * (n * N_BANKS), pIn + idx_col * n,
          core_id, n, n_col * (n >> 2U));
    }
  }
  mempool_log_partial_barrier(2, absolute_core_id, n_col * (n >> 2U));
  return;
}
