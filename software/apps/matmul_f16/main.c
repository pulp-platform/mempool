// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#include "data/data_matmul_f16.h"
#include "kernel/matmul_f16.h"

#define PARALLEL

__fp16 matrix_a[matrix_M * matrix_N]
    __attribute__((aligned((matrix_M * matrix_N) / 2), section(".l1")));
__fp16 matrix_b[matrix_N * matrix_P]
    __attribute__((aligned((matrix_N * matrix_P) / 2), section(".l1")));
__fp16 matrix_c[matrix_M * matrix_P]
    __attribute__((aligned((matrix_M * matrix_P) / 2), section(".l1")));

int volatile error __attribute__((section(".l1")));

void init_matrix(__fp16 *matrix, __fp16 *input, uint32_t num_rows,
                 uint32_t num_columns, uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = core_id; i < (num_columns * num_rows); i += num_cores) {
    matrix[i] = input[i];
  }
  return;
}

int verify_result(__fp16 *__restrict__ Res, __fp16 *__restrict__ Exp,
                  uint32_t M, uint32_t P, uint32_t core_id,
                  uint32_t num_cores) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < M * P; i++) {
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
        printf("ERROR(%d): %x - %x - %x\n", i, *(int32_t *)&dif,
               *(int32_t *)&exp, *(int32_t *)&res);
      }
    }
    // Wait at barrier before checking
    mempool_barrier(num_cores);
  }
  return 0;
}

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize barrier and synchronize
  mempool_barrier_init(core_id);
  if (core_id == 0) {
    error = 0;
  }
  // Initialize Matrices
  init_matrix(matrix_a, A, matrix_M, matrix_N, core_id, num_cores);
  init_matrix(matrix_b, B, matrix_N, matrix_P, core_id, num_cores);
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

#if defined(PARALLEL)
  // Execute function to test.
  mempool_start_benchmark();
  //  matmul_2x2_parallel_f16(matrix_a, matrix_b, matrix_c, matrix_M,
  //                                matrix_N, matrix_P, core_id, num_cores);
  matmul_4x2_parallel_f16vec(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                             matrix_P, core_id, num_cores);
  // dump_id(core_id);
  mempool_stop_benchmark();
  // Wait at barrier before checking
  mempool_barrier(num_cores);
#elif defined(SINGLE)
  if (core_id == 0) {
    // Execute function to test.
    mempool_start_benchmark();
    matmul_2x2_single_f16(matrix_a, matrix_b, matrix_c, matrix_M, matrix_N,
                          matrix_P);
    mempool_stop_benchmark();
  }
  // Wait at barrier before checking
  mempool_barrier(num_cores);
#endif

  verify_result(matrix_c, C, matrix_M, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  return error;
  return 0;
}
