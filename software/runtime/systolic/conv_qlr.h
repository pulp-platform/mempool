// Copyright 2021 ETH Zurich and University of Bologna.
//
// SPDX-License-Identifier: Apache-2.0
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// Author: Gua Hao Khov, ETH Zurich

/* This library implements a simple systolic architecture emulation
 * using global code based orchestration
 */

/* X is an M x N matrix, W is a 3 x 3 matrix and Y is an (M-2) x (N-2) matrix
 * Y = X * W (without zero-padding)
 * Each core loads the whole weight kernel and outputs a row of Y, while loading
 * and passing rows of X to the next core NOTE: M and N must be at least 3 and
 * the kernel size is fixed to 3 x 3
 */

#include "alloc.h"
#include "printf.h"

#define QLR_BASE 0x40010000
#define QLR_CFG_T0 (QLR_BASE | (5 << 5))
#define QLR_CFG_T1 (QLR_BASE | (6 << 5))
#define QLR_CFG_T2 (QLR_BASE | (7 << 5))
#define QLR_CFG_T3 (QLR_BASE | (28 << 5))
#define QLR_CFG_TYPE 0
#define QLR_CFG_REQ 2
#define QLR_CFG_RF 3
#define QLR_CFG_IADDR 4
#define QLR_CFG_OADDR 5

register int32_t qlr_t0 asm("t0");
register int32_t qlr_t1 asm("t1");
register int32_t qlr_t2 asm("t2");

// Array of queue ptrs in row-major order (concatenated kernels)
int32_t *queues_x_0[NUM_CORES];
int32_t *queues_x_1[NUM_CORES];

void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t core_id;
  uint32_t offset;

  for (uint32_t i = 0; i < NUM_CORES; ++i) {
    core_id = core_map[i];
    offset = core_id * 4;
    queues_x_0[i] = (int32_t *)(offset + 0);
    queues_x_1[i] = (int32_t *)(offset + 1);
  }

  // Print out queue addresses
  // printf("queues_x_0\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //   printf("%5d ", queues_x_0[i]);
  // }
  // printf("\n");
  // printf("queues_x_1\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //   printf("%5d ", queues_x_1[i]);
  // }
  // printf("\n");
}

void systolic_conv_front(const uint32_t num_rows, const uint32_t num_cols,
                         int32_t const *__restrict__ X,
                         int32_t const *__restrict__ W,
                         int32_t *__restrict__ Y) {
  int32_t weights[3][3];
  uint32_t qpush_reqs;
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t col;
  register uint32_t y_anchor;
  uint32_t num_cols_y = num_cols - 2;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Calculate queue requests
  if (num_rows == 3) {
    // special case: kernel is at the last row
    qpush_reqs = 0;
  } else if (num_rows > 3) {
    qpush_reqs = (((num_rows - 4) / NUM_CORES) + 1) * num_cols;
  } else {
    return;
  }

  // Configure QLRs
  if (qpush_reqs != 0) {
    qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)qpush_reqs;
    qlr_cfg_t1[QLR_CFG_OADDR] = (int32_t)queues_x_0[1];
    qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)qpush_reqs;
    qlr_cfg_t2[QLR_CFG_OADDR] = (int32_t)queues_x_1[1];
    qlr_cfg_t1[QLR_CFG_TYPE] = 2;
    qlr_cfg_t2[QLR_CFG_TYPE] = 2;
  }

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = 2; row < num_rows; row += NUM_CORES) {
    write_csr(0, row);
    // ------------
    // SET Y ANCHOR
    // ------------
    y_anchor = (row - 2) * num_cols_y;
    // ----------
    // POPULATE 0
    // ----------
    // Load x vector
    qlr_t0 = X[(row - 2) * num_cols + 0];
    qlr_t1 = X[(row - 1) * num_cols + 0];
    qlr_t2 = X[(row - 0) * num_cols + 0];
    // MACs with 1st row of weights
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ----------
    // POPULATE 1
    // ----------
    // Load x vector
    qlr_t0 = X[(row - 2) * num_cols + 1];
    qlr_t1 = X[(row - 1) * num_cols + 1];
    qlr_t2 = X[(row - 0) * num_cols + 1];
    // MACs with 1st row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 0];
      qlr_t1 = X[(row - 1) * num_cols + col + 0];
      qlr_t2 = X[(row - 0) * num_cols + col + 0];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 1];
      qlr_t1 = X[(row - 1) * num_cols + col + 1];
      qlr_t2 = X[(row - 0) * num_cols + col + 1];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
      // -----------
      // ITERATION 2
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 2];
      qlr_t1 = X[(row - 1) * num_cols + col + 2];
      qlr_t2 = X[(row - 0) * num_cols + col + 2];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 2] = acc_y[1];
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    if (col == num_cols - 2) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 0];
      qlr_t1 = X[(row - 1) * num_cols + col + 0];
      qlr_t2 = X[(row - 0) * num_cols + col + 0];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 1];
      qlr_t1 = X[(row - 1) * num_cols + col + 1];
      qlr_t2 = X[(row - 0) * num_cols + col + 1];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
    } else if (col == num_cols - 1) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t0 = X[(row - 2) * num_cols + col + 0];
      qlr_t1 = X[(row - 1) * num_cols + col + 0];
      qlr_t2 = X[(row - 0) * num_cols + col + 0];
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
    }
  }
}

void systolic_conv_mid(const uint32_t kernel_id, const uint32_t num_rows,
                       const uint32_t num_cols, int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y) {
  int32_t weights[3][3];
  uint32_t qpopush_reqs;
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t col;
  register uint32_t y_anchor;
  uint32_t num_cols_y = num_cols - 2;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;
  volatile int32_t *qlr_cfg_t2 = (int32_t *)QLR_CFG_T2;

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Calculate queue requests
  if (num_rows == kernel_id + 3) {
    // special case: kernel is at the last row
    qpopush_reqs = 0;
  } else if (kernel_id + 3 < num_rows) {
    qpopush_reqs = (((num_rows - (kernel_id + 4)) / NUM_CORES) + 1) * num_cols;
  } else {
    return;
  }

  // Configure QLRs
  if (qpopush_reqs != 0) {
    qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)qpopush_reqs;
    qlr_cfg_t0[QLR_CFG_RF] = 3;
    qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)queues_x_0[kernel_id];
    qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)qpopush_reqs;
    qlr_cfg_t1[QLR_CFG_RF] = 3;
    qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)queues_x_1[kernel_id];
    qlr_cfg_t1[QLR_CFG_OADDR] = (int32_t)queues_x_0[kernel_id + 1];
    qlr_cfg_t2[QLR_CFG_REQ] = (int32_t)qpopush_reqs;
    qlr_cfg_t2[QLR_CFG_OADDR] = (int32_t)queues_x_1[kernel_id + 1];
    qlr_cfg_t0[QLR_CFG_TYPE] = 1;
    qlr_cfg_t1[QLR_CFG_TYPE] = 3;
    qlr_cfg_t2[QLR_CFG_TYPE] = 2;
  }

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = kernel_id + 2; row < num_rows; row += NUM_CORES) {
    write_csr(0, row);
    // ------------
    // SET Y ANCHOR
    // ------------
    y_anchor = (row - 2) * num_cols_y;
    // ---------------
    // CONFIG LAST ROW
    // ---------------
    if (row == num_rows - 1) {
      // If kernel lands at last row request one row (qpop only)
      qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)num_cols;
      qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)num_cols;
      qlr_cfg_t0[QLR_CFG_TYPE] = 1;
      qlr_cfg_t1[QLR_CFG_TYPE] = 1;
    }
    // ----------
    // POPULATE 0
    // ----------
    // Load x vector
    qlr_t2 = X[row * num_cols + 0];
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
    // MACs with 1st row of weights
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ----------
    // POPULATE 1
    // ----------
    // Load x vector
    qlr_t2 = X[row * num_cols + 1];
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
    // MACs with 1st row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 1];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
      // -----------
      // ITERATION 2
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 2];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 2] = acc_y[1];
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    if (col == num_cols - 2) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 1];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
    } else if (col == num_cols - 1) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
    }
  }
}

void systolic_conv_end(const uint32_t kernel_id, const uint32_t num_rows,
                       const uint32_t num_cols, int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y) {
  int32_t weights[3][3];
  uint32_t qpop_reqs;
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t col;
  register uint32_t y_anchor;
  uint32_t num_cols_y = num_cols - 2;
  volatile int32_t *qlr_cfg_t0 = (int32_t *)QLR_CFG_T0;
  volatile int32_t *qlr_cfg_t1 = (int32_t *)QLR_CFG_T1;

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Calculate queue requests
  if (kernel_id + 2 < num_rows) {
    qpop_reqs = (((num_rows - (kernel_id + 3)) / NUM_CORES) + 1) * num_cols;
  } else {
    return;
  }

  // Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = (int32_t)qpop_reqs;
  qlr_cfg_t0[QLR_CFG_RF] = 3;
  qlr_cfg_t0[QLR_CFG_IADDR] = (int32_t)queues_x_0[kernel_id];
  qlr_cfg_t1[QLR_CFG_REQ] = (int32_t)qpop_reqs;
  qlr_cfg_t1[QLR_CFG_RF] = 3;
  qlr_cfg_t1[QLR_CFG_IADDR] = (int32_t)queues_x_1[kernel_id];
  qlr_cfg_t0[QLR_CFG_TYPE] = 1;
  qlr_cfg_t1[QLR_CFG_TYPE] = 1;

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = kernel_id + 2; row < num_rows; row += NUM_CORES) {
    write_csr(0, row);
    // ------------
    // SET Y ANCHOR
    // ------------
    y_anchor = (row - 2) * num_cols_y;
    // ----------
    // POPULATE 0
    // ----------
    // Load x vector
    qlr_t2 = X[row * num_cols + 0];
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
    // MACs with 1st row of weights
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ----------
    // POPULATE 1
    // ----------
    // Load x vector
    qlr_t2 = X[row * num_cols + 1];
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
    // MACs with 1st row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t0), "r"(weights[0][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t0), "r"(weights[0][1]));
    __asm__ __volatile__("mul   %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t0), "r"(weights[0][0]));
    // MACs with 2nd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t1), "r"(weights[1][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t1), "r"(weights[1][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t1), "r"(weights[1][0]));
    // MACs with 3rd row of weights
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[1])
                         : "r"(qlr_t2), "r"(weights[2][2]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[2])
                         : "r"(qlr_t2), "r"(weights[2][1]));
    __asm__ __volatile__("p.mac %0, %1, %2"
                         : "+r"(acc_y[0])
                         : "r"(qlr_t2), "r"(weights[2][0]));
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 1];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
      // -----------
      // ITERATION 2
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 2];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 2] = acc_y[1];
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    if (col == num_cols - 2) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 1];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 1] = acc_y[0];
    } else if (col == num_cols - 1) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      qlr_t2 = X[row * num_cols + col + 0];
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));
      // MACs with 1st row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t0), "r"(weights[0][1]));
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][0]));
      // MACs with 2nd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t1), "r"(weights[1][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t1), "r"(weights[1][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t1), "r"(weights[1][0]));
      // MACs with 3rd row of weights
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[2])
                           : "r"(qlr_t2), "r"(weights[2][2]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[0])
                           : "r"(qlr_t2), "r"(weights[2][1]));
      __asm__ __volatile__("p.mac %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t2), "r"(weights[2][0]));
      // Store finished accumulation
      Y[y_anchor + (col - 2) + 0] = acc_y[2];
    }
  }
}
