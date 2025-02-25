// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "archi_redmule.h"
#include "hal_redmule.h"
#include "data_matmul_f16.h"
#include "dma.h"

__fp16 l1_A[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_B[matrix_N * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_C[matrix_M * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id != 0) {
    mempool_wfi();
  }

  dma_memcpy_blocking(l1_A, l2_A, (matrix_M * matrix_N) * sizeof(int16_t));
  dma_memcpy_blocking(l1_B, l2_B, (matrix_N * matrix_P) * sizeof(int16_t));
  dma_memcpy_blocking(l1_C, l2_C, 2*(matrix_M * matrix_P) * sizeof(int16_t));
  printf("Done DMA transfer.\n");

  // Activate RedMulE
  hwpe_soft_clear();
  // Configure RedMulE
  redmule_cfg((unsigned int)l1_A, (unsigned int)l1_B, (unsigned int)l1_C,
    matrix_M, matrix_N, matrix_P, (uint8_t)GEMM, (uint8_t)Float16);

  // Start RedMulE operation and poll the finish until the end of computation
  printf("Triggering accelerator and polling...\n");
  hwpe_trigger_job();

  // Sleep
  mempool_wait(100);
  while (HWPE_READ(REDMULE_FINISHED) != 1) {
    mempool_wait(100);
  }
  printf("Redmule is finished.\n");
  wake_up_all();

  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
