// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "choldecf16.h"
#include "data_choldecf16.h"
__fp16 in_matrix[2 * N_TX * N_RX]    __attribute__((section(".l1")));
__fp16 out_matrix[2 * N_TX * N_RX]   __attribute__((section(".l1")));

void initialize_zeros(__fp16 *matrix, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
void initialize(__fp16 *in_matrix, __fp16 *out_matrix, __fp16 *In,
                uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i++) {
    matrix[i] = (__fp16) (0x0000);
  }
  mempool_barrier(num_cores);
  return;
}

void verify_result(__fp16 *pRes, __fp16 *pExp, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {
      __fp16 error;
      __fp16 exp = pExp[i];
      __fp16 res = pRes[i];
      asm volatile(
        "fsub.h %[error], %[res], %[exp];"
        : [error] "=&r"(error)
        : [res] "r"(res), [exp] "r"(exp)
        : );
      if (*(int32_t*)&error != 0) {
        printf("(%d): 0x%08x - 0x%08x - 0x%08x\n", i / 2, *(int32_t*)&error, *(int32_t*)&exp, *(int32_t*)&res);
      }
    }
  }
}


// Driver program
void single_core() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize
  /* Initialize matrices */
  initialize(in_matrix, In_G, N_RX*N_TX, core_id, num_cores);
  initialize_zeros(out_matrix, N_RX*N_TX, core_id, num_cores);
  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_cholesky_f16s(in_matrix, out_matrix, N_TX);
    mempool_Ltrisol_f16s(out_matrix, b, y, N_TX);
    mempool_Lttrisol_f16s(out_matrix, y, x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  verify_result(out_matrix, Out_L, N_TX * N_RX, core_id);
  mempool_barrier(num_cores);
  return;
}


int main() {
  single_core();
  return 0;
}
