// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "baremetal/mempool_sqrt_q32s.h"
#include "builtins_v2.h"

/** VECTORIZED CODE
  @brief         Cholesky decomposition with Crout algorithm.
  Output data is folded to the core's local memory.
  @param[in]     pSrc  points to input matrix
  @param[in]     pL points to output lower triangular matrix
  @param[in]     n dimension of the input data
  @return        none
*/
void mempool_cholesky_q16vecs(int16_t *pSrc, int16_t *pL, const uint32_t n) {

  uint32_t i, j, k;
  int32_t sum;    // Sum for elements on diagonal (real)
  int32_t diag;   // Diagonal element (real)
  int32_t as, bs; // Sum for elements on rows (complex)
  int32_t ap, bp; // Pivot elements (complex)

  v2s ab = (v2s){0, 0};
  v2s cd = (v2s){0, 0};
  v2s ndc = (v2s){0, 0};
  v2s res = (v2s){0, 0};

  for (j = 0; j < n; j++) {

    // Elements on diagonal (input matrix is positive-definite)
    sum = 0;
    diag = (int32_t)pSrc[2 * (j * n + j)];
    for (k = 0; k < j; k++) {
      ab = *(v2s *)&pL[2 * (j * n + k)];
      asm volatile("pv.dotsp.h %[sum], %[ab],  %[ab];"
                   "srai       %[sum], %[sum],  0x8;"
                   "p.clip     %[sum], %[sum],  0x16;"
                   : [sum] "+&r"(sum)
                   : [ab] "r"(ab)
                   :);
    }
    pL[2U * (j * n + j)] = (int16_t)mempool_sqrt_q32s(diag - sum, 16);

    // Elements on rows
    for (i = j + 1; i < n; i++) {
      ap = (int32_t)pSrc[2 * (i * n + j)];     // Pivot
      bp = (int32_t)pSrc[2 * (i * n + j) + 1]; // Pivot
      diag = (int32_t)pL[2 * (j * n + j)];     // Diag

      as = 0;
      bs = 0;
      // Sum -> s = s + (ac + bd) + j*(bc - ad)
      for (k = 0; k < j; k++) {
        ab = *(v2s *)&pL[2U * (i * n + k)];
        cd = *(v2s *)&pL[2U * (j * n + k)];
        const uint32_t shuffle_mask = 0x00020003;
        asm volatile(
            // s = s + (ac + bd) + j(bc - ad)
            "pv.dotsp.h     %[as],  %[ab],   %[cd];"
            "pv.shuffle2.h  %[ndc], %[cd],   %[shuffle_mask];"
            "pv.sub.h       %[ndc], %[zero], %[ndc];"
            "pv.dotsp.h     %[bs],  %[ab],   %[ndc];"
            "srai           %[as],  %[as],   0x8;"
            "srai           %[bs],  %[bs],   0x8;"
            "p.clip         %[bs],  %[bs],   0x16;"
            "p.clip         %[as],  %[as],   0x16;"
            : [as] "+&r"(as), [bs] "+&r"(bs), [ndc] "+r"(ndc)
            : [ab] "r"(ab), [cd] "r"(cd), [shuffle_mask] "r"(shuffle_mask),
              [zero] "r"((v2s){0, 0})
            :);
      }
      asm volatile("sub       %[ap], %[ap], %[as];"
                   "sub       %[bp], %[bp], %[bs];"
                   "div       %[ap], %[ap], %[diag];"
                   "div       %[bp], %[bp], %[diag];"
                   "pv.pack   %[res], %[ap], %[bp];"
                   : [ap] "+&r"(ap), [bp] "+&r"(bp), [res] "+&r"(res)
                   : [as] "r"(as), [bs] "r"(bs), [diag] "r"(diag)
                   :);
      (*(v2s *)&pL[2 * (i * n + j)]) = res;
    }
  }
  return;
}
