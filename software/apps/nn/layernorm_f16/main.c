// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_layernorm_f16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_layernorm_f16.h"

__fp16 matrix_a[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 matrix_b[matrix_M * matrix_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize matrices
  if (core_id == 0) {
    dma_memcpy_blocking(matrix_a, l2_A,
                        (matrix_M * matrix_N) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  // Matrix Normalization
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(matrix_a, matrix_b, matrix_M, matrix_N, core_id,
                                num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // mempool_check_f16(matrix_b, l2_B, matrix_M * matrix_N, 0.1f, 0);
  mempool_barrier(num_cores);
  return 0;
}
