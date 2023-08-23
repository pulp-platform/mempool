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

/* X is an M x N matrix, W is a 3 x 3 matrix and Y is an M x N matrix
 * Y = X * W (with zero-padding)
 * Each core loads the whole weight kernel and outputs a row of Y, while loading
 * and passing rows of X to the next core
 * NOTE: M and N must be at least 3 and the kernel size is fixed to 3 x 3
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "systolic/queue.h"

// Array of queue ptrs in row-major order (concatenated kernels)
queue_t *queues_x_0[NUM_CORES];
queue_t *queues_x_1[NUM_CORES];

void systolic_init(uint32_t const *tile_map, uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t tile_id;
  alloc_t *alloc;
  // We want all cores connected in a chain, each one taking care of a row
  // Serially connecting all cores in a chain with the order based on their
  // core_id maximizes the systolic links going through the same tile and
  // the same group
  for (uint32_t i = 0; i < NUM_CORES; i++) {
    tile_id = tile_map[i];

    // only 2 queues used (but you want to always use each core's
    // local memory banks, so keep the offset multiple of NUM_QUEUES_PER_CORE)

    alloc = get_alloc_tile(tile_id);
    queue_domain_create(alloc, &queues_x_0[i], 4);
    queue_domain_create(alloc, &queues_x_1[i], 4);
  }
  // Print out queue addresses
  // printf("\n[QUEUE] queues_x_0\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //   printf("%d: %p\n", i, queues_x_0[i]);
  // }
  // printf("\n[QUEUE] queues_x_1\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //   printf("%d: %p\n", i, queues_x_1[i]);
  // }
}

void systolic_conv_front(const uint32_t num_cores, const uint32_t num_rows,
                         const uint32_t num_cols, int32_t const *__restrict__ X,
                         const uint32_t rep_count) {
  queue_t *queue_next_x_0;
  queue_t *queue_next_x_1;
  int32_t qlr_t1, qlr_t2;
  uint32_t row = 0;
  uint32_t col;

  // Assign queues
  queue_next_x_0 = (queue_t *)queues_x_0[1];
  queue_next_x_1 = (queue_t *)queues_x_1[1];

  // Synchronize cores

  for (uint32_t rep = 0; rep < rep_count; ++rep) {
    // Special case: Execute first row of systolic 2d convolution
    // Convolution with only the two lower weight rows

    for (col = 0; col < num_cols; ++col) {
      // Load x vector
      __asm__ __volatile__("li %0, 0" : "=r"(qlr_t1));
      qlr_t2 = X[col];
      // Push lower part of x vector
      blocking_queue_push(queue_next_x_0, &qlr_t1);
      blocking_queue_push(queue_next_x_1, &qlr_t2);
    }

    // Execute row-wise systolic 2d convolution
    for (uint32_t row = (num_cores - 1); row < num_rows;
         row += (num_cores - 1)) {

      for (col = 0; col < num_cols; ++col) {
        // Load x vector
        qlr_t1 = X[(row - 1) * num_cols + col];
        qlr_t2 = X[(row + 0) * num_cols + col];
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
      }
    }
  }
}

void systolic_conv_mid(const uint32_t kernel_id, const uint32_t num_cores,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y,
                       const uint32_t rep_count) {
  queue_t *queue_prev_x_0;
  queue_t *queue_next_x_0;
  queue_t *queue_prev_x_1;
  queue_t *queue_next_x_1;
  int32_t weights[3][3];
  int32_t qlr_t0, qlr_t1, qlr_t2;
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t row, col;

  // Assign queues
  queue_prev_x_0 = (queue_t *)queues_x_0[kernel_id + 1];
  queue_next_x_0 = (queue_t *)queues_x_0[kernel_id + 2];
  queue_prev_x_1 = (queue_t *)queues_x_1[kernel_id + 1];
  queue_next_x_1 = (queue_t *)queues_x_1[kernel_id + 2];

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Synchronize cores

  for (uint32_t rep = 0; rep < rep_count; ++rep) {
    // Execute row-wise systolic 2d convolution
    for (row = kernel_id; row < num_rows - 1; row += (num_cores - 1)) {

      // --------
      // POPULATE
      // --------
      // Pop and load x vector
      blocking_queue_pop(queue_prev_x_0, &qlr_t0);
      qlr_t2 = X[(row + 1) * num_cols];
      blocking_queue_pop(queue_prev_x_1, &qlr_t1);
      // Push lower part of x vector
      blocking_queue_push(queue_next_x_0, &qlr_t1);
      blocking_queue_push(queue_next_x_1, &qlr_t2);
      // MACs with 1st row of weights
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("mul   %0, %1, %2"
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
      for (col = 1; col < num_cols - 2; col += 3) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 1];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col + 0] = acc_y[0];
        // -----------
        // ITERATION 2
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 2];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col + 1] = acc_y[1];
      }
      // ---------------------
      // CONVOLUTION REMAINDER
      // ---------------------
      if (col == num_cols - 2) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 1];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col + 0] = acc_y[0];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 1] = acc_y[1];
      } else if (col == num_cols - 1) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
        // Push lower part of x vector
        blocking_queue_push(queue_next_x_0, &qlr_t1);
        blocking_queue_push(queue_next_x_1, &qlr_t2);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 0] = acc_y[0];
      } else {
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col - 1] = acc_y[2];
      }
    }
    // Special case: Execute last row of systolic 2d convolution
    if (row == num_rows - 1) {
      // Convolution with only the two upper weight rows

      // --------
      // POPULATE
      // --------
      // Pop x vector
      blocking_queue_pop(queue_prev_x_1, &qlr_t1);
      blocking_queue_pop(queue_prev_x_0, &qlr_t0);
      // MACs with 1st row of weights
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("mul   %0, %1, %2"
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
      // ------------------
      // CONVOLUTION BURSTS
      // ------------------
      for (col = 1; col < num_cols - 2; col += 3) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 0] = acc_y[0];
        // -----------
        // ITERATION 2
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 1] = acc_y[1];
      }
      // ---------------------
      // CONVOLUTION REMAINDER
      // ---------------------
      if (col == num_cols - 2) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 0] = acc_y[0];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 1] = acc_y[1];
      } else if (col == num_cols - 1) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 0] = acc_y[0];
      } else {
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col - 1] = acc_y[2];
      }
    }
  }
}

void systolic_conv_end(const uint32_t kernel_id, const uint32_t num_cores,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y,
                       const uint32_t rep_count) {
  queue_t *queue_prev_x_0;
  queue_t *queue_prev_x_1;
  int32_t weights[3][3];
  int32_t qlr_t0, qlr_t1, qlr_t2;
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t row, col;

  // Assign queues
  queue_prev_x_0 = (queue_t *)queues_x_0[kernel_id + 1];
  queue_prev_x_1 = (queue_t *)queues_x_1[kernel_id + 1];

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Synchronize cores

  for (uint32_t rep = 0; rep < rep_count; ++rep) {
    // Execute row-wise systolic 2d convolution
    for (row = kernel_id; row < num_rows - 1; row += (num_cores - 1)) {

      // --------
      // POPULATE
      // --------
      // Pop and load x vector
      blocking_queue_pop(queue_prev_x_1, &qlr_t1);
      qlr_t2 = X[(row + 1) * num_cols];
      blocking_queue_pop(queue_prev_x_0, &qlr_t0);
      // MACs with 1st row of weights
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("mul   %0, %1, %2"
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
      for (col = 1; col < num_cols - 2; col += 3) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 1];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col + 0] = acc_y[0];
        // -----------
        // ITERATION 2
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 2];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col + 1] = acc_y[1];
      }
      // ---------------------
      // CONVOLUTION REMAINDER
      // ---------------------
      if (col == num_cols - 2) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 1];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col + 0] = acc_y[0];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 1] = acc_y[1];
      } else if (col == num_cols - 1) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop and load x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        qlr_t2 = X[(row + 1) * num_cols + col + 0];
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        Y[row * num_cols + col - 1] = acc_y[2];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 0] = acc_y[0];
      } else {
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col - 1] = acc_y[2];
      }
    }
    // Special case: Execute last row of systolic 2d convolution
    if (row == num_rows - 1) {
      // Convolution with only the two upper weight rows

      // --------
      // POPULATE
      // --------
      // Pop x vector
      blocking_queue_pop(queue_prev_x_1, &qlr_t1);
      blocking_queue_pop(queue_prev_x_0, &qlr_t0);
      // MACs with 1st row of weights
      __asm__ __volatile__("mul   %0, %1, %2"
                           : "+r"(acc_y[1])
                           : "r"(qlr_t0), "r"(weights[0][2]));
      __asm__ __volatile__("mul   %0, %1, %2"
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
      // ------------------
      // CONVOLUTION BURSTS
      // ------------------
      for (col = 1; col < num_cols - 2; col += 3) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 0] = acc_y[0];
        // -----------
        // ITERATION 2
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 1] = acc_y[1];
      }
      // ---------------------
      // CONVOLUTION REMAINDER
      // ---------------------
      if (col == num_cols - 2) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // -----------
        // ITERATION 1
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col + 0] = acc_y[0];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 1] = acc_y[1];
      } else if (col == num_cols - 1) {
        // -----------
        // ITERATION 0
        // -----------
        // Pop x vector
        blocking_queue_pop(queue_prev_x_1, &qlr_t1);
        blocking_queue_pop(queue_prev_x_0, &qlr_t0);
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
        // Store finished accumulation
        Y[row * num_cols + col - 1] = acc_y[2];
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col + 0] = acc_y[0];
      } else {
        // Store partial accumulation (zero-padding)
        Y[row * num_cols + col - 1] = acc_y[2];
      }
    }
  }
}
