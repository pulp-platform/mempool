// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "data.h"
#include "dma.h"
#include "encoding.h"
#include "kernel/convolution.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

// #include "convolution_riscv.h"
// #include "halide_runtime.h"

#define M (92)
#define N (4 * NUM_CORES)
#define KERNEL_N 3
// #define VERBOSE

dump(time, 0);
dump(val, 1);
dump(barrier, 2);

volatile int32_t in[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out[M * N] __attribute__((section(".l1_prio")));
volatile int32_t out_l2[M * N] __attribute__((section(".l2"))) __attribute__((aligned(NUM_CORES*BANKING_FACTOR*4)));;
// volatile int32_t kernel[KERNEL_N * KERNEL_N] __attribute__((section(".l1")));



uint32_t dma_log_barrier(uint32_t step, uint32_t log2_radix, uint32_t core_id) {
  uint32_t* log_barrier = (uint32_t *)(((core_id / step) * step + (step >> log2_radix) - 1) * 1024);

  uint32_t val = __atomic_fetch_add(log_barrier, 1, __ATOMIC_RELAXED);
  dump_barrier(step * 1024*1024+(uint32_t)log_barrier + val);
  if (val == (uint32_t)((1 << log2_radix) - 1)) {
    // Last core of this stage
    if (step == NUM_CORES) {
      // Last stage
      // Clear wfi that was triggered by the first core
      mempool_wfi();
      return (uint32_t)log_barrier;
    } else {
      __atomic_store_n(log_barrier, 0, __ATOMIC_RELAXED);
      return dma_log_barrier(step << log2_radix, log2_radix, core_id);
    }
  } else if (val == 0 && step == NUM_CORES) {
    // First core of last stage
    // Check that the DMA from the previous iteration is done
    dma_wait();
    // Wake up all cores to get to work
    wake_up_all();
    mempool_wfi();
  } else {
    // Middle cores, sleep
    mempool_wfi();
  }
  return 0;
}






int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  int32_t kernel[KERNEL_N * KERNEL_N];

  // Initialize img
  if (core_id == 0) {
#ifdef VERBOSE
    printf("Initialize\n");
#endif
    dma_memcpy_blocking((void *)in, (void *)in_l2, M * N / 2 * sizeof(int32_t));
  }

  kernel[0] = 1;
  kernel[1] = 2;
  kernel[2] = 1;

  kernel[3] = 2;
  kernel[4] = 4;
  kernel[5] = 2;

  kernel[6] = 1;
  kernel[7] = 2;
  kernel[8] = 1;

  // Double-buffered convolution
  const int last_round = 6;
  // const int first = 0;
  const int last = (int)4 - 1; // Radix 4 barrier
  int32_t *round_barrier = (int32_t *)(core_id * 1024);

  // Initial setup
  if (core_id != 0) {
    *round_barrier = 0;
    // wake_up_all();
  }

  // Matrices are initialized --> Start calculating
  // Wait at barrier until everyone is ready
  mempool_barrier(num_cores);

  const int32_t *in_comp;
  const int32_t *in_dma;
  int32_t *out_comp;
  int32_t *out_dma;
  for (int round = 0; round < last_round; ++round) {
    if (round % 2 == 0) {
      in_comp = (const int32_t *)&in[0];
      out_comp = (int32_t *)&out[0];
      in_dma = (const int32_t *)&in[N * M / 2];
      out_dma = (int32_t *)&out[N * M / 2];
    } else {
      in_dma = (const int32_t *)&in[0];
      out_dma = (int32_t *)&out[0];
      in_comp = (const int32_t *)&in[N * M / 2];
      out_comp = (int32_t *)&out[N * M / 2];
    }
    mempool_start_benchmark();
    while(*((int32_t *)(63 * 1024)) > last) {
      mempool_wait(num_cores);
    }
    // Barrier, launch DMA for next iteration
    uint32_t bar = dma_log_barrier(4, 2, core_id);
    if (bar) {
      // We are the last one, reset the barrier
      // The old data can now be overwritten with a new DMA request
      if (round != last_round - 1) {
        dma_memcpy_nonblocking((void *)in_dma, (void *)in_l2,
                               M * N / 2 * sizeof(int32_t));
      }
      if (round != 0) {
        dma_memcpy_nonblocking((void *)out_l2, (void *)out_dma,
                               M * N / 2 * sizeof(int32_t));
      }
      // We are the last one, reset the barrier
      __atomic_store_n((uint32_t*)bar, 0, __ATOMIC_RELAXED);
      // __atomic_fetch_add(round_barrier, -num_cores, __ATOMIC_RELAXED);
      // *round_barrier = 0;
      // if (round != last_round - 1) {
      //   wake_up_all();
      // }
    } else {
      // Wait until the core checking the DMA gives the signal
      // mempool_wfi();
    }
    mempool_stop_benchmark();
    mempool_start_benchmark();
    conv2d_3x3_crazy_parallel((const int32_t *)in_comp, N, M / 2,
                              (const int32_t *)kernel, (int32_t *)out_comp,
                              core_id, num_cores);
    mempool_stop_benchmark();
  }

  mempool_start_benchmark();

  // Wait at barrier befor checking
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  // TODO Verify

  return 0;
}
