// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/**
  @brief         Check for f32 kernels.
  @param[in]     pRes points to the result
  @param[in]     pExp points to the expected result
  @param[in]     NEL  number of elements to check
  @param[in]     TOL  floating point tolerance
  @return        none
*/
void mempool_check_f32(float *__restrict__ pRes, float *__restrict__ pExp,
                       uint32_t NEL, float TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();
  float error;
  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      float exp = pExp[i];
      float res = pRes[i];
      asm volatile("fsub.s %[error], %[res], %[exp];"
                   : [error] "+&r"(error)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      bool print = ((error > TOL) || (error < (-TOL))) | verbose;
      if (print) {
        printf("CHECK(%d): EXP = %x - RESP = %x\n", i, *(int32_t *)&exp,
               *(int32_t *)&res);
        ERRORS++;
      }
    }
    printf("\n%d ERRORS out of %d CHECKS\n\n", ERRORS, NEL);
  }
  return;
}

/**
  @brief         Check for f16 kernels.
  @param[in]     pRes points to the result
  @param[in]     pExp points to the expected result
  @param[in]     NEL  number of elements to check
  @param[in]     TOL  floating point tolerance
  @return        none
*/
void mempool_check_f16(__fp16 *__restrict__ pRes, __fp16 *__restrict__ pExp,
                       uint32_t NEL, float TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();
  float error;
  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      __fp16 exp = pExp[i];
      __fp16 res = pRes[i];
      asm volatile("fsub.h %[error], %[res], %[exp];"
                   "fcvt.s.h %[error], %[error];"
                   : [error] "+&r"(error)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      bool print = ((error > TOL) || (error < (-TOL))) | verbose;
      if (print) {
        printf("CHECK(%d): EXP = %x - RESP = %x\n", i, *(int32_t *)&exp,
               *(int32_t *)&res);
        ERRORS++;
      }
    }
    printf("\n%d ERRORS out of %d CHECKS\n\n", ERRORS, NEL);
  }
  return;
}
