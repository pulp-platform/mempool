// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* GAUSS JORDAN ALGORITHM
  - Form the augmented matrix by the identity matrix
  - LOOP OVER ROWS ...
  - Check if the element on the diagonal of the input matrix is zero
    > The element is zero, check if there is a nonzero element in one of the
  rows below on the same column > Exchange the row with the row containing a
  nonzero element on the same column > If there is no such element then the
  matrix is singular and the algorithm fails

  - Divide the current row by the element on the diagonal
  - Replace all the rows below with the sum of that row and a multiple of the
  current row (row i), so that each new element in column i, below row i is
  zero.
*/

#define FIX_MUL(a, b, fp) ((a * b) >> fp)
#define FIX_DIV(a, b, fp) ((a << fp) / b)

int mempool_gaussjordan_q32s(int32_t *pSrc, int32_t *pDst, uint32_t N,
                             uint32_t FP) {

  // Create identity matrix
  for (uint32_t k = 0; k < N; k++) {
    for (uint32_t j = 0; j < N; j++) {
      pDst[k * N + j] = (int32_t)(k == j) << FP;
    }
  }

  // Forward elimination
  for (uint32_t i = 0; i < N; i++) {

    // Find non-zero pivot (swap rows if pivot is zero)
    if (pSrc[i * N + i] == 0) {
      bool pivot_found = false;
      int32_t swp_dst, swp_src;
      /* Loop over the rows present below */
      for (uint32_t k = i + 1U; k < N; k++) {
        if (pSrc[k * N + i] != 0) {
          // swap
          pivot_found = true;
          for (uint32_t j = 0; j < N; j++) {
            swp_src = pSrc[k * N + j];
            swp_dst = pDst[k * N + j];
            pSrc[k * N + j] = pSrc[i * N + j];
            pDst[k * N + j] = pDst[i * N + j];
            pSrc[i * N + j] = swp_src;
            pDst[i * N + j] = swp_dst;
          }
          break;
        }
      }
      /* Return when the matrix is singular */
      if (!pivot_found)
        return 1;
    }

    // Normalize the pivot row
    int32_t pivot = pSrc[i * N + i];
    for (uint32_t j = 0; j < N; j++) {
      pSrc[i * N + j] = FIX_DIV(pSrc[i * N + j], pivot, FP);
      pDst[i * N + j] = FIX_DIV(pDst[i * N + j], pivot, FP);
    }

    // Eliminate other rows
    for (uint32_t j = 0; j < N; j++) {
      if (j != i) {
        int32_t factor = pSrc[j * N + i];
        for (uint32_t k = 0; k < N; k++) {
          pSrc[j * N + k] -= FIX_MUL(factor, pSrc[i * N + k], FP);
          pDst[j * N + k] -= FIX_MUL(factor, pDst[i * N + k], FP);
        }
      }
    }
  }

  return 0;
}

int mempool_gaussjordan_q32p(int32_t *pSrc, int32_t *pDst, uint32_t N,
                             uint32_t FP, uint32_t core_id,
                             uint32_t num_cores) {

  // Create identity matrix
  for (uint32_t k = core_id; k < N; k += num_cores) {
    for (uint32_t j = 0; j < N; j++) {
      pDst[k * N + j] = (int32_t)(k == j) << FP;
    }
  }
  mempool_barrier(num_cores);

  // Forward elimination
  for (uint32_t i = 0; i < N; i++) {

    if (core_id == 0) {
      // Find non-zero pivot (swap rows if pivot is zero)
      if (pSrc[i * N + i] == 0) {
        bool pivot_found = false;
        int32_t swp_dst, swp_src;
        /* Loop over the rows present below */
        for (uint32_t k = i + 1U; k < N; k++) {
          if (pSrc[k * N + i] != 0) {
            // swap
            pivot_found = true;
            for (uint32_t j = 0; j < N; j++) {
              swp_src = pSrc[k * N + j];
              swp_dst = pDst[k * N + j];
              pSrc[k * N + j] = pSrc[i * N + j];
              pDst[k * N + j] = pDst[i * N + j];
              pSrc[i * N + j] = swp_src;
              pDst[i * N + j] = swp_dst;
            }
            break;
          }
        }
        /* Return when the matrix is singular */
        if (!pivot_found)
          return 1;
      }
    }
    mempool_barrier(num_cores);

    // Normalize the pivot row
    int32_t pivot = pSrc[i * N + i];
    for (uint32_t k = core_id; k < N; k += num_cores) {
      pSrc[i * N + k] = FIX_DIV(pSrc[i * N + k], pivot, FP);
      pDst[i * N + k] = FIX_DIV(pDst[i * N + k], pivot, FP);
    }
    mempool_barrier(num_cores);

    // Eliminate other rows
    for (uint32_t j = core_id; j < N; j += num_cores) {
      if (j != i) {
        int32_t factor = pSrc[j * N + i];
        for (uint32_t k = 0; k < N; k++) {
          pSrc[j * N + k] -= FIX_MUL(factor, pSrc[i * N + k], FP);
          pDst[j * N + k] -= FIX_MUL(factor, pDst[i * N + k], FP);
        }
      }
    }
    mempool_barrier(num_cores);
  }

  return 0;
}
