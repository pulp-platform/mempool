// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"
#include "runtime.h"
#include "synchronization.h"

/* Start one RedMulE job: Y (M x P) = X (M x N) * W (N x P), without waiting */
static inline void redmule_start(__fp16 const *X, __fp16 const *W, __fp16 *Y,
                                 uint32_t M, uint32_t N, uint32_t P, uint32_t O,
                                 uint8_t gemm_op) {
  hwpe_soft_clear();
  mempool_wait(10);
  redmule_cfg((unsigned int)X, (unsigned int)W, (unsigned int)Y, (uint16_t)M,
              (uint16_t)N, (uint16_t)P, (uint16_t)O, gemm_op, Float16);
  mempool_wait(10);
  hwpe_trigger_job();
}

static inline void redmule_synch_single(__fp16 *X, __fp16 *W, __fp16 *Y,
                                        uint32_t M, uint32_t N, uint32_t P,
                                        uint8_t gemm_op, uint32_t redmule_id) {

  uint32_t num_cores = mempool_get_core_count();
  if (redmule_id == mempool_get_redmule_id()) {
    redmule_start(X, W, Y, M, N, P, 0, gemm_op);
    mempool_wfi();
  }
  mempool_barrier(num_cores);

  return;
}

static inline void redmule_asynch_single(__fp16 *X, __fp16 *W, __fp16 *Y,
                                         uint32_t M, uint32_t N, uint32_t P,
                                         uint8_t gemm_op, uint32_t redmule_id) {

  if (redmule_id == mempool_get_redmule_id()) {
    redmule_start(X, W, Y, M, N, P, 0, gemm_op);
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

    redmule_start(X + redmule_id * (M * N / num_redmules), W,
                  Y + redmule_id * (M * P / num_redmules), M / num_redmules, N,
                  P, O_shift, gemm_op);
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

    redmule_start(X + redmule_id * (M * N / num_redmules), W,
                  Y + redmule_id * (M * P / num_redmules), M / num_redmules, N,
                  P, O_shift, gemm_op);
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
