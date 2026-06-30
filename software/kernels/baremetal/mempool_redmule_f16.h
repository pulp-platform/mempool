// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"
#include "runtime.h"
#include "synchronization.h"

static inline void redmule_synch_single(__fp16 *X, __fp16 *W, __fp16 *Y,
                                        uint32_t M, uint32_t N, uint32_t P,
                                        uint8_t gemm_op, uint32_t redmule_id) {

  uint32_t num_cores = mempool_get_core_count();
  if (redmule_id == mempool_get_redmule_id()) {

    uint16_t int16M = (uint16_t)M;
    uint16_t int16N = (uint16_t)N;
    uint16_t int16P = (uint16_t)P;
    unsigned int uintX = (unsigned int)(X);
    unsigned int uintY = (unsigned int)(Y);
    unsigned int uintW = (unsigned int)(W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(uintX, uintW, uintY, int16M, int16N, int16P, 0, gemm_op,
                Float16);
    mempool_wait(10);
    hwpe_trigger_job();
    mempool_wfi();
  }
  mempool_barrier(num_cores);

  return;
}

static inline void redmule_asynch_single(__fp16 *X, __fp16 *W, __fp16 *Y,
                                         uint32_t M, uint32_t N, uint32_t P,
                                         uint8_t gemm_op, uint32_t redmule_id) {

  if (redmule_id == mempool_get_redmule_id()) {

    uint16_t int16M = (uint16_t)M;
    uint16_t int16N = (uint16_t)N;
    uint16_t int16P = (uint16_t)P;
    unsigned int uintX = (unsigned int)(X);
    unsigned int uintY = (unsigned int)(Y);
    unsigned int uintW = (unsigned int)(W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(uintX, uintW, uintY, int16M, int16N, int16P, 0, gemm_op,
                Float16);
    mempool_wait(10);
    hwpe_trigger_job();
    mempool_wfi();
  }

  return;
}

static inline void redmule_synch_parallel(__fp16 *X, __fp16 *W, __fp16 *Y,
                                          uint32_t M, uint32_t N, uint32_t P,
                                          uint8_t gemm_op, bool shift,
                                          uint32_t shift_val) {
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  uint32_t num_cores = mempool_get_core_count();

  if (redmule_id < num_redmules) {

    uint32_t X_shift = shift ? (redmule_id * shift_val) % N : 0;
    uint32_t O_shift = shift ? (redmule_id * shift_val) % P : 0;
    X += X_shift;

    uint16_t int16M = (uint16_t)M / num_redmules;
    uint16_t int16N = (uint16_t)N;
    uint16_t int16P = (uint16_t)P;
    uint16_t int16O = (uint16_t)O_shift;
    unsigned int uintX =
        (unsigned int)(X + redmule_id * (M * N / num_redmules));
    unsigned int uintY =
        (unsigned int)(Y + redmule_id * (M * P / num_redmules));
    unsigned int uintW = (unsigned int)(W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(uintX, uintW, uintY, int16M, int16N, int16P, int16O, gemm_op,
                Float16);
    mempool_wait(10);
    hwpe_trigger_job();
    mempool_wfi();
  }
  mempool_barrier(num_cores);

  return;
}

static inline void redmule_asynch_parallel(__fp16 *X, __fp16 *W, __fp16 *Y,
                                           uint32_t M, uint32_t N, uint32_t P,
                                           uint8_t gemm_op, bool shift,
                                           uint32_t shift_val) {
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  if (redmule_id < num_redmules) {

    uint32_t X_shift = shift ? (redmule_id * shift_val) % N : 0;
    uint32_t O_shift = shift ? (redmule_id * shift_val) % P : 0;
    X += X_shift;

    uint16_t int16M = (uint16_t)M / num_redmules;
    uint16_t int16N = (uint16_t)N;
    uint16_t int16P = (uint16_t)P;
    uint16_t int16O = (uint16_t)O_shift;
    unsigned int uintX =
        (unsigned int)(X + redmule_id * (M * N / num_redmules));
    unsigned int uintY =
        (unsigned int)(Y + redmule_id * (M * P / num_redmules));
    unsigned int uintW = (unsigned int)(W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(uintX, uintW, uintY, int16M, int16N, int16P, int16O, gemm_op,
                Float16);
    mempool_wait(10);
    hwpe_trigger_job();
  }

  return;
}

static inline void wait_redmule() {
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  if (redmule_id < num_redmules) {
    mempool_wfi();
  }
  return;
}
