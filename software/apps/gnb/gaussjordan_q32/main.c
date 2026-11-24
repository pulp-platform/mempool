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

#include "data_gaussjordan_q32.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_gaussjordan_q32.h"

int32_t l1_Src[matrix_N * matrix_N] __attribute__((section(".l1_prio")));
int32_t l1_Dst[matrix_N * matrix_N] __attribute__((section(".l1_prio")));

#define PARALLEL

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);
  // Initialize data
  if (core_id == 0) {
    dma_memcpy_blocking(l1_Src, l2_Src, matrix_N * matrix_N * sizeof(int32_t));
  }
  mempool_barrier(num_cores);

/* SINGLE */
#ifdef SINGLE
  if (core_id == 0) {
    mempool_gaussjordan_q32s(l1_Src, l1_Dst, matrix_N, FIXED_POINT);
  }
  mempool_barrier(num_cores);
#endif

/* PARALLEL */
#ifdef PARALLEL
  mempool_gaussjordan_q32p(l1_Src, l1_Dst, matrix_N, FIXED_POINT, core_id,
                           num_cores);
  mempool_barrier(num_cores);
#endif

  mempool_check_i32(l1_Dst, l2_Dst, matrix_N * matrix_N, 1 << (FIXED_POINT - 1),
                    0);
  mempool_barrier(num_cores);

  return 0;
}
