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

#ifdef VERBOSE
dump(res, 8);
#endif

#if (NUM_CORES > 256)
#define ID_REDMULE_CORE (896)
#else
#define ID_REDMULE_CORE (240)
#endif

__fp16 l1_W[matrix_N * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y[matrix_M * matrix_P]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_X[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time_init, time_end;
  mempool_barrier_init(core_id);

  if (core_id == ID_REDMULE_CORE) {

    dma_memcpy_blocking(l1_X, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));

    time_init = mempool_get_timer();
    // Configure RedMulE
    hwpe_soft_clear();
    mempool_wait(10);
    redmule_cfg((unsigned int)l1_X, (unsigned int)l1_W, (unsigned int)l1_Y,
                matrix_M, matrix_N, matrix_P, GEMM, Float16);
    mempool_wait(10);
    // Start RedMulE operation
    hwpe_trigger_job();
    // Go to sleep
    mempool_wfi();
    time_end = mempool_get_timer();

    printf("RedMulE runtime: %d\n", time_end - time_init);
#ifdef VERBOSE
    for (uint32_t i = 0; i < matrix_M * matrix_P; i++) {
      dump_res(*(uint32_t *)&l1_Y[i]);
      dump_res(*(uint32_t *)&l2_Z[i]);
    }
#endif
  }
  mempool_barrier(num_cores);

  mempool_check_f16(l1_Y, l2_Z, matrix_M * matrix_P, 0.05f, 0);
  mempool_barrier(num_cores);
  return 0;
}
