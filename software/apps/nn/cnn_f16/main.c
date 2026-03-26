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

#include "data_cnn_f16.h"

/* Number of subcarriers */
#define FM (32)
/* Number of symbols */
#define FN (16)

/* Input tensor depth */
#define DW_D (512)
/* Pointwise filter depth */
#define PW_D (512)
/* Depthwise filter kernel */
#define DW_K (3)

#define PORT_WIDTH (REDMULE_H * (REDMULE_P + 1))
#define SHIFT (true)
dump(checkpoint, 8);

#include "baremetal/mempool_conv2d_f16.h"
#include "baremetal/mempool_layernorm_f16.h"
#include "baremetal/mempool_relu_f16.h"

// These should be allocated dinamically but we still do not have a malloc
// function that aligns data to the TCDM bounday without a shift from the
// canary. Therefore we allocate them statically.

__fp16 l1_Wpw[DW_D * PW_D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Wdw[DW_K * DW_K * DW_D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_Ipw[FM * FN * DW_D + PORT_WIDTH * NUM_REDMULE_TILES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Opw[FM * FN * DW_D + PORT_WIDTH * NUM_REDMULE_TILES]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

__fp16 l1_Idw[FM * FN * DW_D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_Odw[FM * FN * DW_D]
    __attribute__((aligned(NUM_BANKS * sizeof(int32_t)), section(".l1_prio")));

int main() {

  // Initialization
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    dma_memcpy_blocking(l1_Wpw, l2_W, DW_D * PW_D * sizeof(int16_t));
    dma_memcpy_blocking(l1_Wdw, l2_W, DW_D * DW_K * DW_K * sizeof(int16_t));
    dma_memcpy_blocking(l1_Opw, l2_Y, FM * FN * DW_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);

#ifdef DOUBLE_BUFFERING

  // Transfer input and output previous iteration
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1_Ipw, l2_X, FM * FN * DW_D * sizeof(int16_t));
    dma_memcpy_blocking(l2_Y, l1_Opw, FM * FN * PW_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(0);

  // TEs Compute 2D convolution on the current iteration
  mempool_start_benchmark();
  redmule_asynch_parallel(l1_Ipw, l1_Opw, l1_Wpw,
    FM * FN, DW_D, PW_D, GEMM, SHIFT, PORT_WIDTH);
  mempool_stop_benchmark();

  dump_checkpoint(1);

  // PEs Compute 2D convolution on the current iteration
  mempool_start_benchmark();
  conv2d_depthwise_f16(l1_Idw, l1_Odw, l1_Wdw,
    FM, FN, DW_D, DW_K, core_id, num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(2);

  // Wait for all TEs and for all PEs
  mempool_start_benchmark();
  wait_redmule();
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(3);

  // Layernorm
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(l1_Opw, l1_Idw,
    FM * FN, PW_D, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(4);

  // ReLU
  mempool_start_benchmark();
  relu_f16(l1_Opw, FM * FN * PW_D, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(5);

#else

  uint32_t redmule_id = mempool_get_redmule_id();
  uint32_t num_redmules = mempool_get_redmule_count();

  // Transfer input
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l1_Ipw, l2_X, FM * FN * DW_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(0);

  // PEs Compute 2D convolution on the current iteration
  mempool_start_benchmark();
  conv2d_depthwise_f16(l1_Idw, l1_Odw, l1_Wdw,
    FM, FN, DW_D, DW_K, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(1);

  // TEs Compute 2D convolution on the current iteration
  mempool_start_benchmark();
  redmule_synch_parallel(l1_Ipw, l1_Opw, l1_Wpw,
    FM * FN, DW_D, PW_D, GEMM, SHIFT, PORT_WIDTH);
  mempool_stop_benchmark();

  dump_checkpoint(2);

  // Layernorm
  mempool_start_benchmark();
  layernorm_parallel_2x4_f16vec(l1_Opw, l1_Idw,
    FM * FN, PW_D, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(3);

  // ReLU
  mempool_start_benchmark();
  relu_f16(l1_Opw, FM * FN * PW_D, core_id, num_cores);
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(4);

  // Transfer output
  mempool_start_benchmark();
  if (core_id == 0) {
    dma_memcpy_blocking(l2_Y, l1_Opw, FM * FN * PW_D * sizeof(int16_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  dump_checkpoint(5);

#endif

  return 0;
}
