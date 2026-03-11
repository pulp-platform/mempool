// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_axpy_f8.h"

#include "baremetal/mempool_axpy_f8.h"
#include "baremetal/mempool_checks.h"

__fp8 l1_X[array_N] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));
__fp8 l1_Y[array_N] __attribute__((aligned(NUM_BANKS), section(".l1_prio")));

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t time_init, time_end;
  mempool_barrier_init(core_id);

  time_init = 0;
  time_end = 0;
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X, l2_X, array_N * sizeof(int8_t));
    dma_memcpy_blocking(l1_Y, l2_Y, array_N * sizeof(int8_t));
  }
  uint32_t register volatile a = *(uint32_t *)&(l2_A)&0x0000FFFF;
  mempool_barrier(num_cores);

  // PARALLEL, LOCAL ACCESSES
  time_init = mempool_get_timer();
  mempool_start_benchmark();
  axpy_f8vec_local_unrolled4(a, l1_X, l1_Y, array_N);
  mempool_stop_benchmark();
  time_end = mempool_get_timer();

  mempool_barrier(num_cores);
  // Check results
  if (core_id == 0) {
    uint32_t clock_cycles = (time_end - time_init);
    printf("\nKernel execution takes %d clock cycles\n", clock_cycles);
  }
  mempool_check_f8(l1_Y, l2_Z, array_N, 0x34, 0); // tol = 0.25 = 0x34 (__fp8)
  mempool_barrier(num_cores);

  return 0;
}
