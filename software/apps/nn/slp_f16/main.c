// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_checks.h"
#include "baremetal/mempool_redmule_f16.h"
#include "baremetal/mempool_softmax_f16.h"

#include "data_slp_f16.h"

#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (true)

__fp16 l1_W[matrix_N * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_X_A[(matrix_M * matrix_N) + PORT_WIDTH * NUM_REDMULE_TILES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y_A[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_Z[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_S[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_X_B[(matrix_M * matrix_N) + PORT_WIDTH * NUM_REDMULE_TILES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Y_B[matrix_M * matrix_P]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

/* Dump execution checkpoint */
dump(checkpoint, 8);

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

#ifdef DOUBLE_BUFFERING

  /* (itr. + 0): Transfer input and weights */
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X_A, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y_A, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Z, l2_Z, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  /* Transfer input (itr. + 1) */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_nonblocking(l1_X_B, l2_X,
      (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_nonblocking(l1_Y_B, l2_Y,
      (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_stop_benchmark();

  dump_checkpoint(0);

  /* GEMM */
  mempool_start_benchmark();
  redmule_asynch_parallel(l1_X_A, l1_Y_A, l1_W,
    matrix_M, matrix_N, matrix_P, GEMM, SHIFT, PORT_WIDTH);
  mempool_stop_benchmark();

  dump_checkpoint(1);

  /* Softmax */
  mempool_start_benchmark();
  softmax_parallel_2x4_f16vec(l1_Z, l1_S,
    matrix_M, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(2);

  /* Transfer output (itr. - 1) */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_nonblocking(
      l2_S, l1_S, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_stop_benchmark();

  dump_checkpoint(3);

  mempool_start_benchmark();
  /* Wait RedMulE */
  wait_redmule();
  /* Wait DMA */
  if (core_id == 0) {
    dma_wait();
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  /* Check */
  mempool_check_f16(l1_Y_A, l2_Z, 100, 0.1f, 1);
  mempool_barrier(num_cores);

#else

  if (core_id == 0) {
    dma_memcpy_blocking(l1_W, l2_W, (matrix_N * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

  /* DMA */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1_X_A, l2_X, (matrix_M * matrix_N) * sizeof(int16_t));
    dma_memcpy_blocking(l1_Y_A, l2_Y, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(0);

  /* GEMM */
  mempool_start_benchmark();
  redmule_synch_parallel(l1_X_A, l1_Y_A, l1_W,
    matrix_M, matrix_N, matrix_P, GEMM, SHIFT, PORT_WIDTH);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(1);

  /* Softmax */
  mempool_start_benchmark();
  softmax_parallel_2x4_f16vec(l1_Y_A, l1_S,
    matrix_M, matrix_P, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(2);

  /* Check */
  mempool_check_f16(l1_Y_A, l2_Z, 100, 0.1f, 1);
  mempool_check_f16(l1_S, l2_S, 100, 0.1f, 1);
  mempool_barrier(num_cores);

  dump_checkpoint(3);

  /* DMA */
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l2_S, l1_S, (matrix_M * matrix_P) * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

#endif

  return 0;
}
