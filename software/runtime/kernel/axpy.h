// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the dot product kernel
 */

#pragma once
#include "dma.h"
#include "runtime.h"

// Must match the unroll factor in the code
#define AXPY_UNROLL (4)

void axpy_parallel(const int32_t *x, int32_t *y, int32_t alpha, uint32_t N,
                   uint32_t core_id, uint32_t num_cores) {
  for (uint32_t i = AXPY_UNROLL * core_id; i < N;
       i += AXPY_UNROLL * num_cores) {
    y[i + 0] = alpha * x[i + 0] + y[i + 0];
    y[i + 1] = alpha * x[i + 1] + y[i + 1];
    y[i + 2] = alpha * x[i + 2] + y[i + 2];
    y[i + 3] = alpha * x[i + 3] + y[i + 3];
  }
}

void axpy_parallel_asm(const int32_t *x, int32_t *y, int32_t alpha, uint32_t N,
                       uint32_t core_id, uint32_t num_cores) {
  int32_t x0, x1, x2, x3, y0, y1, y2, y3;

  const int32_t *addr_x = &x[AXPY_UNROLL * core_id];
  const int32_t *addr_y = &y[AXPY_UNROLL * core_id];
  const int32_t *end_x = &x[AXPY_UNROLL * core_id + N];

  const uint32_t row_increment =
      (AXPY_UNROLL * num_cores - AXPY_UNROLL + 1) * 4;

  __asm__ volatile(
      // ".balign 16 \n\t"
      // Inner loop: Do this loop N times
      "1: \n\t"
      // Load values
      "p.lw %[x0], %[COLUMN](%[addr_x]!) \n\t"
      "p.lw %[y0], %[COLUMN](%[addr_y]!) \n\t"
      "p.lw %[x1], %[COLUMN](%[addr_x]!) \n\t"
      "p.lw %[y1], %[COLUMN](%[addr_y]!) \n\t"
      "p.lw %[x2], %[COLUMN](%[addr_x]!) \n\t"
      "p.lw %[y2], %[COLUMN](%[addr_y]!) \n\t"
      "p.lw %[x3], %[ROW](%[addr_x]!) \n\t"
      "p.lw %[y3], %[DECR](%[addr_y]!) \n\t"
      // Do MACs
      "p.mac %[y0], %[alpha], %[x0] \n\t"
      "p.mac %[y1], %[alpha], %[x1] \n\t"
      "p.mac %[y2], %[alpha], %[x2] \n\t"
      "p.mac %[y3], %[alpha], %[x3] \n\t"
      // Write back
      "p.sw %[y0], %[COLUMN](%[addr_y]!) \n\t"
      "p.sw %[y1], %[COLUMN](%[addr_y]!) \n\t"
      "p.sw %[y2], %[COLUMN](%[addr_y]!) \n\t"
      "p.sw %[y3], %[ROW](%[addr_y]!) \n\t"
      "bne %[addr_x], %[end_x], 1b \n\t"
      : [x0] "=&r"(x0), [x1] "=&r"(x1), [x2] "=&r"(x2), [x3] "=&r"(x3),
        [y0] "=&r"(y0), [y1] "=&r"(y1), [y2] "=&r"(y2), [y3] "=&r"(y3),
        [addr_x] "+&r"(addr_x), [addr_y] "+&r"(addr_y) // Outputs
      : [alpha] "r"(alpha), [end_x] "r"(end_x), [ROW] "r"(row_increment),
        [DECR] "I"(-4 * (AXPY_UNROLL - 1)), [COLUMN] "I"(4) // Inputs
      : "memory");                                          // Clobber
}

// void axpy_parallel_dma(const int32_t *a, const int32_t *b, uint32_t N,
//                        const int32_t *a_remote, const int32_t *b_remote,
//                        uint32_t N_remote, int32_t *c, uint32_t core_id,
//                        uint32_t num_cores) {
//   int32_t *axpy_barrier_a = (int32_t *)(64 * 1024);
//   int32_t *axpy_barrier_b = (int32_t *)(192 * 1024);
//   int32_t tmp_sum[AXPY_UNROLL] = {0, 0, 0, 0};

//   uint32_t first = 0;
//   uint32_t last = 2 * num_cores;
//   int last_round = 2;

//   // Initial setup
//   if (core_id == 0) {
//     wake_up_all();
//   }

//   for (int round = 0; round < last_round; ++round) {
//     // Barrier, launch DMA for next iteration
//     mempool_wfi();
//     int bar = __atomic_fetch_add(axpy_barrier_a, 2, __ATOMIC_RELAXED);
//     // Are we the first to reach the next round?
//     if (bar == first) {
//       dma_wait();
//       dma_memcpy_nonblocking(a, a_remote, N * sizeof(int32_t));
//       dma_memcpy_nonblocking(b, b_remote, N * sizeof(int32_t));
//       bar = __atomic_fetch_add(axpy_barrier_a, 2, __ATOMIC_RELAXED);
//     }
//     // Are we the last one?
//     if (bar == last) {
//       *axpy_barrier_a = 0;
//       if (round != last_round - 1) {
//         wake_up_all();
//       }
//     }

//     for (uint32_t i = AXPY_UNROLL * core_id; i < N;
//          i += AXPY_UNROLL * num_cores) {
//       tmp_sum[0] += a[i + 0] * b[i + 0];
//       tmp_sum[1] += a[i + 1] * b[i + 1];
//       tmp_sum[2] += a[i + 2] * b[i + 2];
//       tmp_sum[3] += a[i + 3] * b[i + 3];
//     }
//   }
//   int32_t sum = tmp_sum[0];
//   sum += tmp_sum[1];
//   sum += tmp_sum[2];
//   sum += tmp_sum[3];
//   __atomic_fetch_add(c, sum, __ATOMIC_RELAXED);
// }
