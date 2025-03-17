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
#include "data_gemm_f16.h"
#include "dma.h"
#include "baremetal/mempool_checks.h"

dump(res, 8);

__fp16 l1_X[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_W[matrix_N * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y[matrix_M * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  if (core_id != 0) {
    mempool_wfi();
  }
  dma_memcpy_blocking(l1_X, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
  dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
  dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  // Configure RedMulE
  hwpe_soft_clear();
  redmule_cfg((unsigned int) l1_X, (unsigned int) l1_W, (unsigned int) l1_Y, matrix_M, matrix_N, matrix_P, GEMM, Float16);
  // Start RedMulE operation
  hwpe_trigger_job();
  // Go to sleep
  mempool_wfi();
  for (uint32_t i = 0; i < matrix_M * matrix_P; i++) {
    dump_res(*(uint32_t*)&l1_Y[i]);
    dump_res(*(uint32_t*)&l2_Z[i]);
  }
  wake_up_all();

  return 0;
}
