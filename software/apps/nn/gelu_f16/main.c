// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "dma.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_gelu_f16.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_gelu_f16.h"

__fp16 l1_data[array_N]
    __attribute__((aligned(NUM_CORES * sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();

  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1_data, l2_A, sizeof(l1_data));
  }
  mempool_barrier(num_cores);

  mempool_start_benchmark();
  gelu_f16(l1_data, array_N, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  mempool_check_f16(l1_data, l2_B, array_N, 0.01f, 0);
  mempool_barrier(num_cores);
  return 0;
}
