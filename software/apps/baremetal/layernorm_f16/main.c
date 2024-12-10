// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_layernorm_f16.h"
#include "data_layernorm_f16.h"

__fp16 l1_X[array_N]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

float l1_eps __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
float l1_gamma __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
float l1_beta __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices 1
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, (array_N) * sizeof(int16_t));
    l1_eps = eps;
    l1_gamma = gamma;
    l1_beta = beta;
  }
  mempool_barrier(num_cores);

  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    layernorm_f16s_unrolled4(l1_X, l1_X, array_N, l1_eps, l1_gamma, l1_beta,
                             RELU);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  mempool_check_f16(l1_X, l2_Y, array_N, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
