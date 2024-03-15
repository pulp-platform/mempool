// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/**
  @brief         Check for q32 kernels.
  @param[in]     pRes points to the result
  @param[in]     pExp points to the expected result
  @param[in]     NEL  number of elements to check
  @param[in]     TOL  floating point tolerance
  @return        none
*/
void mempool_check_q32(int32_t *__restrict__ pRes, int32_t *__restrict__ pExp,
                       uint32_t NEL, int32_t TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();
  int32_t error;
  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      int32_t exp = pExp[i];
      int32_t res = pRes[i];
      error = exp - res;
      bool print = ((error > TOL) || (error < (-TOL))) || verbose;
      if (print) {
        printf("CHECK(%d): EXP = %08X - RESP = %08X\n", i, exp, res);
        ERRORS++;
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
  }
  return;
}

/**
  @brief         Check for q16 kernels.
  @param[in]     pRes points to the result
  @param[in]     pExp points to the expected result
  @param[in]     NEL  number of elements to check
  @param[in]     TOL  floating point tolerance
  @return        none
*/
void mempool_check_q16(int16_t *__restrict__ pRes, int16_t *__restrict__ pExp,
                       uint32_t NEL, int16_t TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();
  int16_t error;
  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      int16_t exp = (int16_t)pExp[i];
      int16_t res = (int16_t)pRes[i];
      error = (int16_t)(exp - res);
      bool print = ((error > TOL) || (error < (-TOL))) | verbose;
      if (print) {
        printf("CHECK(%d): EXP = %08X - RESP = %08X\n", i, exp, res);
        ERRORS++;
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
  }
  return;
}
