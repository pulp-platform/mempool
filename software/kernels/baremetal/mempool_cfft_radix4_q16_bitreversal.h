// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

void mempool_bitrev_q16p_xpulpimg(uint16_t *pSrc, uint16_t *pDst,
                                  const uint16_t fftLen, const uint32_t nPE) {
  uint32_t absolute_core_id = mempool_get_core_id();
  uint32_t core_id = absolute_core_id / WU_STRIDE;
  uint32_t idx_result, idx, i, j;
  for (i = core_id; i < fftLen; i += nPE) {
    idx_result = 0;
    idx = i;
    for (j = 0; j < LOG2; j++) {
      idx_result = (idx_result << 1U) | (idx & 1U);
      idx = idx >> 1U;
    }
    pDst[2 * idx_result] = pSrc[2 * i];
    pDst[2 * idx_result + 1] = pSrc[2 * i + 1];
  }
  mempool_log_partial_barrier(2 * WU_STRIDE, absolute_core_id, nPE * WU_STRIDE);
}
