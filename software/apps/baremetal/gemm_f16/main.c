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

#define ELEMENTS_PER_ROW (NUM_BANKS * sizeof(int32_t) / sizeof(int16_t) )
#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))

__fp16 l1_X[(matrix_M * matrix_N) + PORT_WIDTH*NUM_REDMULE_TILES*(NUM_REDMULE_TILES+1)]
    __attribute__((aligned(NUM_BANKS*sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[matrix_N * matrix_P]
    __attribute__((aligned(NUM_BANKS*sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS*sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();
  mempool_barrier_init(core_id);

#ifdef SINGLE
  // Transfer
  if (redmule_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  // Compute
  if (redmule_id == 0) {
    unsigned int X_ptr = (unsigned int) (l1_X);
    unsigned int Y_ptr = (unsigned int) (l1_Y);
    unsigned int W_ptr = (unsigned int) (l1_W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(X_ptr, W_ptr, Y_ptr, matrix_M, matrix_N, matrix_P, 0, GEMM, Float16);
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

#ifdef PARALLEL

  uint32_t X_shift;
  uint32_t W_shift;

  // Transfer
  if (redmule_id == 0) {
    for (uint32_t i = 0; i < num_redmules; i++) {
      X_shift = (XSHIFT == 1) ? (i * PORT_WIDTH) % matrix_N : 0;
      dma_memcpy_blocking(
          l1_X + i * (matrix_M * matrix_N / num_redmules) + X_shift,
          l2_X + i * (matrix_M * matrix_N / num_redmules),
          (matrix_M * matrix_N / num_redmules) * sizeof(int16_t)
      );
    }
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  // Compute
  if (redmule_id < num_redmules) {
    X_shift = (XSHIFT == 1) ? (redmule_id * PORT_WIDTH) % matrix_N : 0;
    W_shift = (WSHIFT == 1) ? (redmule_id * PORT_WIDTH) % matrix_P : 0;
    unsigned int X_ptr = (unsigned int) (l1_X + redmule_id * (matrix_M * matrix_N / num_redmules) + X_shift);
    unsigned int Y_ptr = (unsigned int) (l1_Y + redmule_id * (matrix_M * matrix_P / num_redmules));
    unsigned int W_ptr = (unsigned int) (l1_W);
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg(X_ptr, W_ptr, Y_ptr, (matrix_M / num_redmules), matrix_N, matrix_P, W_shift, GEMM, Float16);
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

  mempool_check_f16(l1_Y, l2_Z, 10, 0.05f, 0);
  mempool_barrier(num_cores);
  return 0;
}
