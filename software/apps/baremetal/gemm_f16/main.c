// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "archi_redmule.h"
#include "hal_redmule.h"

#include "baremetal/mempool_checks.h"
#include "data_gemm_f16.h"

#define ELEMENTS_PER_ROW (NUM_BANKS * sizeof(int32_t) / sizeof(int16_t))
#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))

#ifndef SINGLE
#ifndef PARALLEL
#ifndef PARALLEL_BATCHED
#define SINGLE
#endif
#endif
#endif

#ifdef PARALLEL_BATCHED
__fp16 l1_X[Batch * matrix_M * matrix_N]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[Batch * matrix_N * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y[Batch * matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
#else
__fp16 l1_X[(matrix_M * matrix_N) + 2 * PORT_WIDTH * NUM_REDMULE_TILES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[matrix_N * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
#endif

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t redmule_id = mempool_get_redmule_id();
  mempool_barrier_init(core_id);

#ifdef SINGLE
  // Transfer
  if (redmule_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  static uint32_t time_start, time_end;
  // Compute
  if (redmule_id == 0) {
    time_start = mempool_get_timer();
    unsigned int X_ptr = (unsigned int)(l1_X);
    unsigned int Y_ptr = (unsigned int)(l1_Y);
    unsigned int W_ptr = (unsigned int)(l1_W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(X_ptr, W_ptr, Y_ptr, matrix_M, matrix_N, matrix_P, 0, GEMM,
                Float16);
    mempool_wait(10);
    // Start RedMulE operation
    hwpe_trigger_job();
    // Go to sleep
    mempool_wfi();
  }
  mempool_barrier(num_cores);
  if (redmule_id == 0) {
    time_end = mempool_get_timer();
    printf("TIME: %d\n", time_end - time_start);
  }
#endif

#ifdef PARALLEL

  uint32_t X_shift;
  uint16_t W_shift;
  uint32_t num_redmules = mempool_get_redmule_count();

  // Transfer
  if (redmule_id == 0) {
    for (uint32_t i = 0; i < num_redmules; i++) {
      X_shift = (XSHIFT == 1) ? (i * PORT_WIDTH) % matrix_N : 0;
      dma_memcpy_blocking(
          l1_X + i * (matrix_M * matrix_N / num_redmules) + X_shift,
          l2_X + i * (matrix_M * matrix_N / num_redmules),
          (matrix_M * matrix_N / num_redmules) * sizeof(int16_t));
    }
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  // Compute
  if (redmule_id < num_redmules) {
    X_shift = (XSHIFT == 1) ? (redmule_id * 2 * PORT_WIDTH) % matrix_N : 0;
    W_shift = (WSHIFT == 1) ? (redmule_id * 2 * PORT_WIDTH) % matrix_P : 0;
    unsigned int X_ptr =
        (unsigned int)(l1_X +
                       redmule_id * (matrix_M * matrix_N / num_redmules) +
                       X_shift);
    unsigned int Y_ptr =
        (unsigned int)(l1_Y +
                       redmule_id * (matrix_M * matrix_P / num_redmules));
    unsigned int W_ptr = (unsigned int)(l1_W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(X_ptr, W_ptr, Y_ptr, (matrix_M / num_redmules), matrix_N,
                matrix_P, W_shift, GEMM, Float16);
    mempool_wait(10);
    mempool_start_benchmark();
    // Start RedMulE operation
    hwpe_trigger_job();
    // Go to sleep
    mempool_wfi();
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

#ifdef PARALLEL_BATCHED

  uint32_t num_redmules = mempool_get_redmule_count();

  // Transfer
  // l2_X/l2_W/l2_Y only hold one (M,N,P) GEMM's worth of data
  // (gendata_header.py isn't Batch-aware) -- copy that same source into
  // each of the Batch slots of l1_X/l1_W/l1_Y instead of generating/
  // duplicating Batch-sized L2 data.
  if (redmule_id == 0) {
    for (uint32_t ii = 0; ii < Batch; ii++) {
      dma_memcpy_blocking(l1_X + ii * matrix_M * matrix_N, l2_X,
                           (matrix_M * matrix_N) * sizeof(int16_t));
      dma_memcpy_blocking(l1_W + ii * matrix_N * matrix_P, l2_W,
                           (matrix_N * matrix_P) * sizeof(int16_t));
      dma_memcpy_blocking(l1_Y + ii * matrix_M * matrix_P, l2_Y,
                           (matrix_M * matrix_P) * sizeof(int16_t));
    }
  }
  mempool_barrier(num_cores);
  static uint32_t time_start, time_end;

  if (redmule_id == 0) {
    time_start = mempool_get_timer();
  }

  // Compute
  for (uint32_t ii = redmule_id; ii < Batch; ii += num_redmules) {
    if (redmule_id < num_redmules) {
      unsigned int X_ptr = l1_X + ii * matrix_M * matrix_N;
      unsigned int Y_ptr = l1_Y + ii * matrix_M * matrix_P;
      unsigned int W_ptr = l1_W + ii * matrix_N * matrix_P;
      hwpe_soft_clear();
      mempool_wait(10);
      redmule_cfg(X_ptr, W_ptr, Y_ptr, matrix_M, matrix_N, matrix_P, 0, GEMM, Float16);
      mempool_wait(10);
      // Start RedMulE operation
      hwpe_trigger_job();
      // Go to sleep
      mempool_wfi();
    }
  }
  mempool_barrier(num_cores);

  if (redmule_id == 0) {
    time_end = mempool_get_timer();
    printf("TIME: %d\n", time_end - time_start);
  }

#endif

  mempool_check_f16(l1_Y, l2_Z, 10, 0.05f, 0);
  mempool_barrier(num_cores);
  return 0;
}
