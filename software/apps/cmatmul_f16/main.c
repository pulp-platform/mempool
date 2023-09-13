// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data_cmatmul_f16.h"
#include "kernel/cmatmul_f16.h"
#define PARALLEL


__fp16 matrix_a[2 * matrix_M * matrix_N] __attribute__((section(".l1")));
__fp16 matrix_b[2 * matrix_N * matrix_P] __attribute__((section(".l1")));
__fp16 matrix_c[2 * matrix_M * matrix_P] __attribute__((section(".l1")));

void init_matrix(__fp16 *matrix, __fp16 *input, uint32_t N, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < N; i += num_cores) {
    v2h in = *(v2h*)&input[2 * i];
    (*(v2h*)&matrix[2 * i]) = in;
  }
  return;
}

int verify_result(__fp16 *__restrict__ Res, __fp16 *__restrict__ Exp,
                  uint32_t N, uint32_t core_id,
                  uint32_t num_cores) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < N; i++) {
      __fp16 exp = Exp[i];
      __fp16 res = Res[i];
      __fp16 dif;
      float tol = (__fp16)0.05f;
      float dif_f32;
      asm volatile("fsub.h %[dif], %[res], %[exp];"
                   "fcvt.h.s %[dif_f32], %[dif];"
                   : [dif] "+&r"(dif), [dif_f32] "+&r"(dif_f32)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      if ((dif_f32 > tol) || (dif_f32 < (-tol))) {
        printf("ERROR(%d): %x - %x\n", i, *(int32_t *)&exp, *(int32_t *)&res);
      }
    }
  }
  // Wait at barrier before checking
  mempool_barrier(num_cores);
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);

  // Initialize Matrices
  init_matrix(matrix_a, A, matrix_M * matrix_N, core_id, num_cores);
  init_matrix(matrix_b, B, matrix_N * matrix_P, core_id, num_cores);
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#if defined(SINGLE)
  // Execute function to test.
  if (core_id == 0) {
    mempool_start_benchmark();
    cmatmul_2x4_f16s(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                    matrix_P);
    mempool_stop_benchmark();
  }
#endif

#if defined(PARALLEL)
  // Execute function to test.
  mempool_start_benchmark();
  cmatmul_2x4_f16p(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
#endif

  // Wait at barrier before checking
  mempool_barrier(num_cores);
  verify_result(matrix_c, C, 2*matrix_M*matrix_P, core_id, num_cores);
  return 0;
}
