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
void mempool_check_i32(int32_t *__restrict__ pRes, int32_t *__restrict__ pExp,
                       uint32_t NEL, int32_t TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();

  if (core_id == 0) {

    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      int32_t exp = pExp[i];
      int32_t res = pRes[i];
      int32_t diff = exp - res;
      uint32_t error = ((diff > TOL) || (diff < (-TOL))) ? 1 : 0;
      uint32_t print = error || verbose;
      ERRORS += error;
      if (print) {
        printf("CHECK(%d): EXP = %08X - RESP = %08X\n", i, exp, res);
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
void mempool_check_i16(int16_t *__restrict__ pRes, int16_t *__restrict__ pExp,
                       uint32_t NEL, int16_t TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();

  if (core_id == 0) {

    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      int16_t exp = (int16_t)pExp[i];
      int16_t res = (int16_t)pRes[i];
      int16_t diff = (int16_t)(exp - res);
      uint32_t error = ((diff > TOL) || (diff < (-TOL))) ? 1 : 0;
      uint32_t print = error || verbose;
      ERRORS += error;
      if (print) {
        printf("CHECK(%d): EXP = %04X - RESP = %04X\n", i, exp, res);
        ERRORS++;
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
  }
  return;
}

/**
  @brief         Check for i8 kernels.
  @param[in]     pRes points to the result
  @param[in]     pExp points to the expected result
  @param[in]     NEL  number of elements to check
  @param[in]     TOL  floating point tolerance
  @return        none
*/
void mempool_check_i8(int8_t *__restrict__ pRes, int8_t *__restrict__ pExp,
                      uint32_t NEL, int16_t TOL, bool verbose) {
  uint32_t core_id = mempool_get_core_id();
  int16_t error;
  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      int16_t exp = (int8_t)pExp[i];
      int16_t res = (int8_t)pRes[i];
      error = (int8_t)(exp - res);
      bool print = ((error > TOL) || (error < (-TOL))) | verbose;
      if (print) {
        printf("CHECK(%d): EXP = %02X - RESP = %02X\n", i, exp, res);
        ERRORS++;
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
  }
  return;
}

#ifdef __clang__
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

  if (core_id == 0) {

    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      float exp = pExp[i];
      float res = pRes[i];
      float diff;
      asm volatile("fsub.s %[diff], %[res], %[exp];"
                   : [diff] "+&r"(diff)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      uint32_t error = ((diff > TOL) || (diff < (-TOL))) ? 1 : 0;
      uint32_t print = error || verbose;
      ERRORS += error;
      if (print) {
        printf("CHECK(%d): EXP = %08X - RESP = %08X\n", i, *(int32_t *)&exp,
               *(int32_t *)&res);
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
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

  if (core_id == 0) {
    uint32_t ERRORS = 0;
    for (uint32_t i = 0; i < NEL; i++) {
      __fp16 exp = pExp[i];
      __fp16 res = pRes[i];
      float diff;
      asm volatile("fsub.h %[diff], %[res], %[exp];"
                   "fcvt.s.h %[diff], %[diff];"
                   : [diff] "+&r"(diff)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);

      uint32_t error = ((diff > TOL) || (diff < (-TOL))) ? 1 : 0;
      uint32_t print = error || verbose;
      ERRORS += error;
      if (print) {
        printf("CHECK(%d): EXP = %08X - RESP = %08X\n", i, *(int32_t *)&exp,
               *(int32_t *)&res);
      }
    }
    printf("%d ERRORS out of %d CHECKS\n", ERRORS, NEL);
  }
  return;
}
#endif
