// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Gua Hao Khov, ETH Zurich

/* This library implements a simple systolic architecture emulation
 * using global code based orchestration
 */

/* X is an M x N matrix, W is a 3 x 3 matrix and Y is an (M-2) x (N-2) matrix
 * Y = X * W (without zero-padding)
 * Each core loads the whole weight kernel and outputs a row of Y, while loading
 * and passing rows of X to the next core NOTE: N must be at least 4 and the
 * kernel size is fixed to 3 x 3
 */

// FIXME: Does not work with GCC -O3 optimization as only a limited number of
// outstanding queue ops are supported

#include "alloc.h"
#include "printf.h"

// Queue dump macro
dump(queue, 16);

// Array of queue ptrs in row-major order (concatenated kernels)
int32_t *queues_x_0[NUM_CORES];
int32_t *queues_x_1[NUM_CORES];

// queue push
static inline void queue_push(void *const queue, int32_t data,
                              int32_t *const ret) {
  asm volatile("q.push.w %0, %1, (%2)"
               : "+r"(*ret)
               : "r"(data), "r"(queue)
               : "memory");
}

// queue pop
inline void queue_pop(void *const queue, int32_t *const ret) {
  asm volatile("q.pop.w %0, 0(%1)" : "=r"(*ret) : "r"(queue) : "memory");
}

void systolic_init(uint32_t const *tile_map, uint32_t const *core_map) {
  // Create systolic array via queues
  extern int32_t __seq_start;
  uint32_t tile_id;
  uint32_t core_id;
  uint32_t tile_offset;
  uint32_t core_offset;

  for (uint32_t i = 0; i < NUM_CORES; ++i) {
    tile_id = tile_map[i];
    core_id = core_map[i];
    tile_offset = tile_id * NUM_CORES_PER_TILE * SEQ_MEM_SIZE / sizeof(int32_t);
    core_offset = core_id % NUM_CORES_PER_TILE * 4;
    queues_x_0[i] = &__seq_start + tile_offset + core_offset + 0;
    queues_x_1[i] = &__seq_start + tile_offset + core_offset + 1;
  }

  // Print out queue addresses
  // printf("\n[QUEUE] queues_x_0\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //  dump_queue((uint32_t)(queues_x_0[i]));
  //}
  // printf("\n[QUEUE] queues_x_1\n");
  // for (uint32_t i = 0; i < NUM_CORES; ++i) {
  //  dump_queue((uint32_t)(queues_x_1[i]));
  //}
}

void systolic_conv_front(const uint32_t num_rows, const uint32_t num_cols,
                         int32_t const *__restrict__ X,
                         int32_t const *__restrict__ W,
                         int32_t *__restrict__ Y) {
  int32_t *queue_next_x_0;
  int32_t *queue_next_x_1;
  int32_t resp_x_0 __attribute__((unused)) = 0;
  int32_t resp_x_1 __attribute__((unused)) = 0;
  int32_t weights[3][3];
  int32_t curr_x[3];
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t row;
  uint32_t col;
  uint32_t num_cols_y = num_cols - 2;

  // Assign queues
  queue_next_x_0 = queues_x_0[1];
  queue_next_x_1 = queues_x_1[1];

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Execute row-wise systolic 2d convolution
  row = 2;
  while (row < num_rows - 1) {
    // ----------
    // POPULATE 0
    // ----------
    // Load x vector
    curr_x[1] = X[(row - 1) * num_cols + 0];
    curr_x[2] = X[(row - 0) * num_cols + 0];
    curr_x[0] = X[(row - 2) * num_cols + 0];
    // Push lower part of x vector
    queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
    queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
    // MACs with 1st column of weights
    acc_y[2] += curr_x[0] * weights[0][0];
    acc_y[2] += curr_x[1] * weights[1][0];
    acc_y[2] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ----------
    // POPULATE 1
    // ----------
    // Load x vector
    curr_x[1] = X[(row - 1) * num_cols + 1];
    curr_x[2] = X[(row - 0) * num_cols + 1];
    curr_x[0] = X[(row - 2) * num_cols + 1];
    // Push lower part of x vector
    queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
    queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
    // MACs with 1st row of weights
    acc_y[2] += curr_x[0] * weights[0][1];
    acc_y[0] += curr_x[0] * weights[0][0];
    // MACs with 2nd row of weights
    acc_y[2] += curr_x[1] * weights[1][1];
    acc_y[0] += curr_x[1] * weights[1][0];
    // MACs with 3rd row of weights
    acc_y[2] += curr_x[2] * weights[2][1];
    acc_y[0] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 0];
      curr_x[2] = X[(row - 0) * num_cols + col + 0];
      curr_x[0] = X[(row - 2) * num_cols + col + 0];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 0] = acc_y[2];
      // Reset finished accumulation
      acc_y[2] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 1];
      curr_x[2] = X[(row - 0) * num_cols + col + 1];
      curr_x[0] = X[(row - 2) * num_cols + col + 1];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 1] = acc_y[0];
      // Reset finished accumulation
      acc_y[0] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 2
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 2];
      curr_x[2] = X[(row - 0) * num_cols + col + 2];
      curr_x[0] = X[(row - 2) * num_cols + col + 2];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[1] += curr_x[0] * weights[0][2];
      acc_y[2] += curr_x[0] * weights[0][1];
      acc_y[0] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[1] += curr_x[1] * weights[1][2];
      acc_y[2] += curr_x[1] * weights[1][1];
      acc_y[0] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[1] += curr_x[2] * weights[2][2];
      acc_y[2] += curr_x[2] * weights[2][1];
      acc_y[0] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 2] = acc_y[1];
      // Reset finished accumulation
      acc_y[1] = 0;
      __asm__ __volatile__("" ::: "memory");
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    __asm__ __volatile__("" ::: "memory");
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    while (col < num_cols) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 0];
      curr_x[2] = X[(row - 0) * num_cols + col + 0];
      curr_x[0] = X[(row - 2) * num_cols + col + 0];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[2];
      // Increment column index
      ++col;
      if (col >= num_cols)
        break;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 1];
      curr_x[2] = X[(row - 0) * num_cols + col + 1];
      curr_x[0] = X[(row - 2) * num_cols + col + 1];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[0];
    }
    // ------------------
    // RESET ACCUMULATORS
    // ------------------
    acc_y[0] = 0;
    acc_y[1] = 0;
    acc_y[2] = 0;
    // -------------
    // INCREMENT ROW
    // -------------
    row += NUM_CORES;
  }

  // Finish last row of systolic 2d convolution without pushing
  if (row == num_rows - 1) {
    // ----------
    // POPULATE 0
    // ----------
    // Load x vector
    curr_x[1] = X[(row - 1) * num_cols + 0];
    curr_x[2] = X[(row - 0) * num_cols + 0];
    curr_x[0] = X[(row - 2) * num_cols + 0];
    // MACs with 1st column of weights
    acc_y[2] += curr_x[0] * weights[0][0];
    acc_y[2] += curr_x[1] * weights[1][0];
    acc_y[2] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ----------
    // POPULATE 1
    // ----------
    // Load x vector
    curr_x[1] = X[(row - 1) * num_cols + 1];
    curr_x[2] = X[(row - 0) * num_cols + 1];
    curr_x[0] = X[(row - 2) * num_cols + 1];
    // MACs with 1st row of weights
    acc_y[2] += curr_x[0] * weights[0][1];
    acc_y[0] += curr_x[0] * weights[0][0];
    // MACs with 2nd row of weights
    acc_y[2] += curr_x[1] * weights[1][1];
    acc_y[0] += curr_x[1] * weights[1][0];
    // MACs with 3rd row of weights
    acc_y[2] += curr_x[2] * weights[2][1];
    acc_y[0] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 0];
      curr_x[2] = X[(row - 0) * num_cols + col + 0];
      curr_x[0] = X[(row - 2) * num_cols + col + 0];
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 0] = acc_y[2];
      // Reset finished accumulation
      acc_y[2] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 1];
      curr_x[2] = X[(row - 0) * num_cols + col + 1];
      curr_x[0] = X[(row - 2) * num_cols + col + 1];
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 1] = acc_y[0];
      // Reset finished accumulation
      acc_y[0] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 2
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 2];
      curr_x[2] = X[(row - 0) * num_cols + col + 2];
      curr_x[0] = X[(row - 2) * num_cols + col + 2];
      // MACs with 1st row of weights
      acc_y[1] += curr_x[0] * weights[0][2];
      acc_y[2] += curr_x[0] * weights[0][1];
      acc_y[0] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[1] += curr_x[1] * weights[1][2];
      acc_y[2] += curr_x[1] * weights[1][1];
      acc_y[0] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[1] += curr_x[2] * weights[2][2];
      acc_y[2] += curr_x[2] * weights[2][1];
      acc_y[0] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 2] = acc_y[1];
      // Reset finished accumulation
      acc_y[1] = 0;
      __asm__ __volatile__("" ::: "memory");
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    __asm__ __volatile__("" ::: "memory");
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    while (col < num_cols) {
      // -----------
      // ITERATION 0
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 0];
      curr_x[2] = X[(row - 0) * num_cols + col + 0];
      curr_x[0] = X[(row - 2) * num_cols + col + 0];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[2];
      // Increment column index
      ++col;
      if (col >= num_cols)
        break;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Load x vector
      curr_x[1] = X[(row - 1) * num_cols + col + 1];
      curr_x[2] = X[(row - 0) * num_cols + col + 1];
      curr_x[0] = X[(row - 2) * num_cols + col + 1];
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[0];
    }
  }
}

void systolic_conv_mid(const uint32_t kernel_id, const uint32_t num_rows,
                       const uint32_t num_cols, int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y) {
  int32_t *queue_prev_x_0;
  int32_t *queue_next_x_0;
  int32_t *queue_prev_x_1;
  int32_t *queue_next_x_1;
  int32_t resp_x_0 __attribute__((unused)) = 0;
  int32_t resp_x_1 __attribute__((unused)) = 0;
  int32_t weights[3][3];
  int32_t curr_x[3];
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t row;
  uint32_t col;
  uint32_t num_cols_y = num_cols - 2;

  // Assign queues
  queue_prev_x_0 = queues_x_0[kernel_id];
  queue_next_x_0 = queues_x_0[kernel_id + 1];
  queue_prev_x_1 = queues_x_1[kernel_id];
  queue_next_x_1 = queues_x_1[kernel_id + 1];

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Execute row-wise systolic 2d convolution
  row = kernel_id + 2;
  while (row < num_rows - 1) {
    // ----------
    // POPULATE 0
    // ----------
    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 0];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // Push lower part of x vector
    queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
    queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
    // MACs with 1st column of weights
    acc_y[2] += curr_x[0] * weights[0][0];
    acc_y[2] += curr_x[1] * weights[1][0];
    acc_y[2] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ----------
    // POPULATE 1
    // ----------
    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 1];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // Push lower part of x vector
    queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
    queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
    // MACs with 1st row of weights
    acc_y[2] += curr_x[0] * weights[0][1];
    acc_y[0] += curr_x[0] * weights[0][0];
    // MACs with 2nd row of weights
    acc_y[2] += curr_x[1] * weights[1][1];
    acc_y[0] += curr_x[1] * weights[1][0];
    // MACs with 3rd row of weights
    acc_y[2] += curr_x[2] * weights[2][1];
    acc_y[0] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 0];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 0] = acc_y[2];
      // Reset finished accumulation
      acc_y[2] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 1];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 1] = acc_y[0];
      // Reset finished accumulation
      acc_y[0] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 2
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 2];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[1] += curr_x[0] * weights[0][2];
      acc_y[2] += curr_x[0] * weights[0][1];
      acc_y[0] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[1] += curr_x[1] * weights[1][2];
      acc_y[2] += curr_x[1] * weights[1][1];
      acc_y[0] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[1] += curr_x[2] * weights[2][2];
      acc_y[2] += curr_x[2] * weights[2][1];
      acc_y[0] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 2] = acc_y[1];
      // Reset finished accumulation
      acc_y[1] = 0;
      __asm__ __volatile__("" ::: "memory");
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    __asm__ __volatile__("" ::: "memory");
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    while (col < num_cols) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[2];
      // Increment column index
      ++col;
      if (col >= num_cols)
        break;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // Push lower part of x vector
      queue_push(queue_next_x_0, curr_x[1], &resp_x_0);
      queue_push(queue_next_x_1, curr_x[2], &resp_x_1);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[0];
    }
    // ------------------
    // RESET ACCUMULATORS
    // ------------------
    acc_y[0] = 0;
    acc_y[1] = 0;
    acc_y[2] = 0;
    // -------------
    // INCREMENT ROW
    // -------------
    row += NUM_CORES;
  }

  // Finish last row of systolic 2d convolution without pushing
  if (row == num_rows - 1) {
    // ----------
    // POPULATE 0
    // ----------
    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 0];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // MACs with 1st column of weights
    acc_y[2] += curr_x[0] * weights[0][0];
    acc_y[2] += curr_x[1] * weights[1][0];
    acc_y[2] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ----------
    // POPULATE 1
    // ----------
    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 1];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // MACs with 1st row of weights
    acc_y[2] += curr_x[0] * weights[0][1];
    acc_y[0] += curr_x[0] * weights[0][0];
    // MACs with 2nd row of weights
    acc_y[2] += curr_x[1] * weights[1][1];
    acc_y[0] += curr_x[1] * weights[1][0];
    // MACs with 3rd row of weights
    acc_y[2] += curr_x[2] * weights[2][1];
    acc_y[0] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 0];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 0] = acc_y[2];
      // Reset finished accumulation
      acc_y[2] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 1];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 1] = acc_y[0];
      // Reset finished accumulation
      acc_y[0] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 2
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 2];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[1] += curr_x[0] * weights[0][2];
      acc_y[2] += curr_x[0] * weights[0][1];
      acc_y[0] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[1] += curr_x[1] * weights[1][2];
      acc_y[2] += curr_x[1] * weights[1][1];
      acc_y[0] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[1] += curr_x[2] * weights[2][2];
      acc_y[2] += curr_x[2] * weights[2][1];
      acc_y[0] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 2] = acc_y[1];
      // Reset finished accumulation
      acc_y[1] = 0;
      __asm__ __volatile__("" ::: "memory");
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    __asm__ __volatile__("" ::: "memory");
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    while (col < num_cols) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[2];
      // Increment column index
      ++col;
      if (col >= num_cols)
        break;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[0];
    }
  }
}

void systolic_conv_end(const uint32_t kernel_id, const uint32_t num_rows,
                       const uint32_t num_cols, int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y) {
  int32_t *queue_prev_x_0;
  int32_t *queue_prev_x_1;
  int32_t weights[3][3];
  int32_t curr_x[3];
  register int32_t acc_y[3] = {0, 0, 0};
  uint32_t col;
  uint32_t num_cols_y = num_cols - 2;

  // Assign queues
  queue_prev_x_0 = queues_x_0[kernel_id];
  queue_prev_x_1 = queues_x_1[kernel_id];

  // Load weights
  for (uint32_t y = 0; y < 3; ++y) {
    for (uint32_t x = 0; x < 3; ++x) {
      weights[y][x] = W[y * 3 + x];
    }
  }

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = kernel_id + 2; row < num_rows; row += NUM_CORES) {
    // ----------
    // POPULATE 0
    // ----------

    curr_x[2] = X[row * num_cols + 0];
    asm volatile(
        "q.pop.w %[curr_x_1], 0(%[queue_1]) \n\t"
        "q.pop.w %[curr_x_0], 0(%[queue_0]) \n\t"
        "p.mac %[acc_y_2],  \n\t"
        : [curr_x_0] "=r"(curr_x[0]), [curr_x_1] "=r"(curr_x[1]),
          [acc_y_2] "+r"(acc_y[2])
        : [queue_0] "r"(queue_prev_x_0), [queue_1] "r"(queue_prev_x_1),
          [curr_x_2] "r"(curr_x[2])[weight_0_0] "r"(weights[0][0]),
          [weight_1_0] "r"(weights[1][0]), [weight_2_0] "r"(weights[2][0])
        : "memory");

    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 0];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // MACs with 1st column of weights
    acc_y[2] += curr_x[0] * weights[0][0];
    acc_y[2] += curr_x[1] * weights[1][0];
    acc_y[2] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ----------
    // POPULATE 1
    // ----------
    // Pop and load x vector
    queue_pop(queue_prev_x_1, &curr_x[1]);
    curr_x[2] = X[row * num_cols + 1];
    queue_pop(queue_prev_x_0, &curr_x[0]);
    // MACs with 1st row of weights
    acc_y[2] += curr_x[0] * weights[0][1];
    acc_y[0] += curr_x[0] * weights[0][0];
    // MACs with 2nd row of weights
    acc_y[2] += curr_x[1] * weights[1][1];
    acc_y[0] += curr_x[1] * weights[1][0];
    // MACs with 3rd row of weights
    acc_y[2] += curr_x[2] * weights[2][1];
    acc_y[0] += curr_x[2] * weights[2][0];
    __asm__ __volatile__("" ::: "memory");
    // ------------------
    // CONVOLUTION BURSTS
    // ------------------
    col = 2;
    while (col < num_cols_y) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 0];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 0] = acc_y[2];
      // Reset finished accumulation
      acc_y[2] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 1];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 1] = acc_y[0];
      // Reset finished accumulation
      acc_y[0] = 0;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 2
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col + 2];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[1] += curr_x[0] * weights[0][2];
      acc_y[2] += curr_x[0] * weights[0][1];
      acc_y[0] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[1] += curr_x[1] * weights[1][2];
      acc_y[2] += curr_x[1] * weights[1][1];
      acc_y[0] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[1] += curr_x[2] * weights[2][2];
      acc_y[2] += curr_x[2] * weights[2][1];
      acc_y[0] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2) + 2] = acc_y[1];
      // Reset finished accumulation
      acc_y[1] = 0;
      __asm__ __volatile__("" ::: "memory");
      // ----------------
      // INCREMENT COLUMN
      // ----------------
      col += 3;
    }
    __asm__ __volatile__("" ::: "memory");
    // ---------------------
    // CONVOLUTION REMAINDER
    // ---------------------
    while (col < num_cols) {
      // -----------
      // ITERATION 0
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[2] += curr_x[0] * weights[0][2];
      acc_y[0] += curr_x[0] * weights[0][1];
      acc_y[1] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[2] += curr_x[1] * weights[1][2];
      acc_y[0] += curr_x[1] * weights[1][1];
      acc_y[1] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[2] += curr_x[2] * weights[2][2];
      acc_y[0] += curr_x[2] * weights[2][1];
      acc_y[1] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[2];
      // Increment column index
      ++col;
      if (col >= num_cols)
        break;
      __asm__ __volatile__("" ::: "memory");
      // -----------
      // ITERATION 1
      // -----------
      // Pop and load x vector
      queue_pop(queue_prev_x_1, &curr_x[1]);
      curr_x[2] = X[row * num_cols + col];
      queue_pop(queue_prev_x_0, &curr_x[0]);
      // MACs with 1st row of weights
      acc_y[0] += curr_x[0] * weights[0][2];
      acc_y[1] += curr_x[0] * weights[0][1];
      acc_y[2] += curr_x[0] * weights[0][0];
      // MACs with 2nd row of weights
      acc_y[0] += curr_x[1] * weights[1][2];
      acc_y[1] += curr_x[1] * weights[1][1];
      acc_y[2] += curr_x[1] * weights[1][0];
      // MACs with 3rd row of weights
      acc_y[0] += curr_x[2] * weights[2][2];
      acc_y[1] += curr_x[2] * weights[2][1];
      acc_y[2] += curr_x[2] * weights[2][0];
      // Store finished accumulation
      Y[(row - 2) * num_cols_y + (col - 2)] = acc_y[0];
    }
    // ------------------
    // RESET ACCUMULATORS
    // ------------------
    acc_y[0] = 0;
    acc_y[1] = 0;
    acc_y[2] = 0;
  }
}
