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

/* TODO DESCRIPTION
 *
 *
 *
 *
 *
 *
 */

#include "alloc.h"
#include "printf.h"

// Kernel size (fixed)
#define KERNEL_SIZE 3

// Number of kernels
#define NUM_KERNELS 25

// Array of queue ptrs in row-major order (concatenated kernels)
int32_t *queues_x[KERNEL_SIZE][NUM_KERNELS * KERNEL_SIZE];
int32_t *queues_y[KERNEL_SIZE][NUM_KERNELS * KERNEL_SIZE];
int32_t *queues_row_acc[KERNEL_SIZE][NUM_KERNELS];

// queue push
static inline void queue_push(void *const queue, int32_t data,
                              int32_t *const ret) {
  asm volatile("q.push.w %0, %1, (%2)" : "+r"(*ret) : "r"(data), "r"(queue));
}

// queue pop
inline void queue_pop(void *const queue, int32_t *const ret) {
  asm volatile("q.pop.w %0, 0(%1)" : "=r"(*ret) : "r"(queue));
}

void systolic_init(uint32_t const *kernel_tile_map,
                   uint32_t const *kernel_core_map,
                   uint32_t const *row_acc_tile_map,
                   uint32_t const *row_acc_core_map) {
  // Create systolic array via queues
  extern int32_t __seq_start;
  uint32_t grid_pos;
  uint32_t tile_id;
  uint32_t core_id;
  uint32_t tile_offset;
  uint32_t core_offset;

  // Kernel queues
  grid_pos = 0;
  for (uint32_t y = 0; y < KERNEL_SIZE; ++y) {
    for (uint32_t x = 0; x < NUM_KERNELS * KERNEL_SIZE; ++x) {
      tile_id = kernel_tile_map[grid_pos];
      core_id = kernel_core_map[grid_pos];
      tile_offset = tile_id * 4 * SEQ_MEM_SIZE / 4;
      core_offset = core_id % 4 * 4;
      queues_x[y][x] = &__seq_start + tile_offset + core_offset + 0;
      queues_y[y][x] = &__seq_start + tile_offset + core_offset + 1;
      ++grid_pos;
    }
  }

  // Row accumulator queues
  grid_pos = 0;
  for (uint32_t x = 0; x < NUM_KERNELS; ++x) {
    tile_id = row_acc_tile_map[x];
    core_id = row_acc_core_map[x];
    tile_offset = tile_id * 4 * SEQ_MEM_SIZE / 4;
    core_offset = core_id % 4 * 4;
    queues_row_acc[0][x] = &__seq_start + tile_offset + core_offset + 0;
    queues_row_acc[1][x] = &__seq_start + tile_offset + core_offset + 1;
    queues_row_acc[2][x] = &__seq_start + tile_offset + core_offset + 2;
  }

  // Print out queue addresses
  // printf("queues_x\n");
  // for (uint32_t y = 0; y < KERNEL_SIZE; ++y) {
  //   for (uint32_t x = 0; x < NUM_KERNELS * KERNEL_SIZE; ++x) {
  //     printf("%5d ", queues_x[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_y\n");
  // for (uint32_t y = 0; y < KERNEL_SIZE; ++y) {
  //   for (uint32_t x = 0; x < NUM_KERNELS * KERNEL_SIZE; ++x) {
  //     printf("%5d ", queues_y[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_row_acc\n");
  // for (uint32_t y = 0; y < KERNEL_SIZE; ++y) {
  //   for (uint32_t x = 0; x < NUM_KERNELS; ++x) {
  //     printf("%5d ", queues_row_acc[y][x]);
  //   }
  //   printf("\n");
  // }
}

void systolic_conv_first_front(const uint32_t kernel_id,
                               const uint32_t kernel_row,
                               const uint32_t num_rows, const uint32_t num_cols,
                               int32_t const *__restrict__ X,
                               int32_t const *__restrict__ W) {
  int32_t *queue_next_x;
  int32_t *queue_next_y;
  int32_t resp_x __attribute__((unused)) = 0;
  int32_t resp_y __attribute__((unused)) = 0;
  int32_t weight;
  int32_t curr_x;
  int32_t curr_y;
  uint32_t first_row = kernel_id + kernel_row;
  uint32_t last_row = num_rows - KERNEL_SIZE + kernel_row + 1;

  // Assign queues
  queue_next_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 1];
  queue_next_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 1];

  // Load weight
  weight = W[kernel_row * KERNEL_SIZE + 0];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = first_row; row < last_row; row += NUM_KERNELS) {
    // Populate kernel
    curr_x = X[row * num_cols + 0];
    queue_push(queue_next_x, curr_x, &resp_x);
    curr_x = X[row * num_cols + 1];
    queue_push(queue_next_x, curr_x, &resp_x);
    curr_x = X[row * num_cols + 2];
    // Convolution
    for (uint32_t col = 3; col < num_cols; ++col) {
      queue_push(queue_next_x, curr_x, &resp_x);
      curr_y = curr_x * weight;
      curr_x = X[row * num_cols + col];
      queue_push(queue_next_y, curr_y, &resp_y);
    }
    // Flush kernel
    queue_push(queue_next_x, curr_x, &resp_x);
    curr_y = curr_x * weight;
    queue_push(queue_next_y, curr_y, &resp_y);
  }
}

void systolic_conv_front(const uint32_t kernel_id, const uint32_t kernel_row,
                         const uint32_t num_rows, const uint32_t num_cols,
                         int32_t const *__restrict__ W) {
  int32_t *queue_prev_x;
  int32_t *queue_next_x;
  int32_t *queue_next_y;
  int32_t resp_x __attribute__((unused)) = 0;
  int32_t resp_y __attribute__((unused)) = 0;
  int32_t weight;
  int32_t curr_x;
  int32_t curr_y;
  uint32_t first_row = kernel_id + kernel_row;
  uint32_t last_row = num_rows - KERNEL_SIZE + kernel_row + 1;

  // Assign queues
  queue_prev_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 0];
  queue_next_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 1];
  queue_next_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 1];

  // Load weight
  weight = W[kernel_row * KERNEL_SIZE + 0];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = first_row; row < last_row; row += NUM_KERNELS) {
    // Populate kernel
    queue_pop(queue_prev_x, &curr_x);
    queue_push(queue_next_x, curr_x, &resp_x);
    queue_pop(queue_prev_x, &curr_x);
    queue_push(queue_next_x, curr_x, &resp_x);
    queue_pop(queue_prev_x, &curr_x);
    // Convolution
    for (uint32_t col = 3; col < num_cols; ++col) {
      queue_push(queue_next_x, curr_x, &resp_x);
      curr_y = curr_x * weight;
      queue_pop(queue_prev_x, &curr_x);
      queue_push(queue_next_y, curr_y, &resp_y);
    }
    // Flush kernel
    queue_push(queue_next_x, curr_x, &resp_x);
    curr_y = curr_x * weight;
    queue_push(queue_next_y, curr_y, &resp_y);
  }
}

void systolic_conv_mid(const uint32_t kernel_id, const uint32_t kernel_row,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ W) {
  int32_t *queue_prev_x;
  int32_t *queue_next_x;
  int32_t *queue_prev_y;
  int32_t *queue_next_y;
  int32_t resp_x __attribute__((unused)) = 0;
  int32_t resp_y __attribute__((unused)) = 0;
  int32_t weight;
  int32_t curr_x;
  int32_t curr_y;
  uint32_t first_row = kernel_id + kernel_row;
  uint32_t last_row = num_rows - KERNEL_SIZE + kernel_row + 1;

  // Assign queues
  queue_prev_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 1];
  queue_next_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 2];
  queue_prev_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 1];
  queue_next_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 2];

  // Load weight
  weight = W[kernel_row * KERNEL_SIZE + 1];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = first_row; row < last_row; row += NUM_KERNELS) {
    // Populate kernel
    queue_pop(queue_prev_x, &curr_x);
    queue_push(queue_next_x, curr_x, &resp_x);
    queue_pop(queue_prev_x, &curr_x);
    // Convolution
    for (uint32_t col = 2; col < num_cols; ++col) {
      queue_pop(queue_prev_y, &curr_y);
      queue_push(queue_next_x, curr_x, &resp_x);
      curr_y += curr_x * weight;
      queue_pop(queue_prev_x, &curr_x);
      queue_push(queue_next_y, curr_y, &resp_y);
    }
    // Flush kernel
    queue_push(queue_next_x, curr_x, &resp_x);
  }
}

void systolic_conv_end(const uint32_t kernel_id, const uint32_t kernel_row,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ W) {
  int32_t *queue_prev_x;
  int32_t *queue_next_x;
  int32_t *queue_prev_y;
  int32_t *queue_next_y;
  int32_t resp_x __attribute__((unused)) = 0;
  int32_t resp_y __attribute__((unused)) = 0;
  int32_t weight;
  int32_t curr_x;
  int32_t curr_y;
  uint32_t first_row = kernel_id + kernel_row;
  uint32_t last_row = num_rows - KERNEL_SIZE + kernel_row + 1;

  // Assign queues
  queue_prev_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 2];
  queue_next_x = queues_x[kernel_row + 1][(kernel_id + 1) * KERNEL_SIZE];
  queue_prev_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 2];
  queue_next_y = queues_row_acc[kernel_row][kernel_id];

  // Load weight
  weight = W[kernel_row * KERNEL_SIZE + 2];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = first_row; row < last_row; row += NUM_KERNELS) {
    // Populate kernel
    queue_pop(queue_prev_x, &curr_x);
    // Convolution
    for (uint32_t col = 1; col < num_cols - 1; ++col) {
      queue_pop(queue_prev_y, &curr_y);
      queue_push(queue_next_x, curr_x, &resp_x);
      curr_y += curr_x * weight;
      queue_pop(queue_prev_x, &curr_x);
      queue_push(queue_next_y, curr_y, &resp_y);
    }
    // Flush kernel
    queue_push(queue_next_x, curr_x, &resp_x);
    queue_pop(queue_prev_x, &curr_x);
    queue_push(queue_next_x, curr_x, &resp_x);
  }

  // Flush next queues at the end of execution
  queue_pop(queue_next_x, &curr_x);
  queue_pop(queue_next_x, &curr_x);
}

void systolic_conv_last_end(const uint32_t kernel_id, const uint32_t kernel_row,
                            const uint32_t num_rows, const uint32_t num_cols,
                            int32_t const *__restrict__ W) {
  int32_t *queue_prev_x;
  int32_t *queue_prev_y;
  int32_t *queue_next_y;
  int32_t resp_y __attribute__((unused)) = 0;
  int32_t weight;
  int32_t curr_x;
  int32_t curr_y;
  uint32_t first_row = kernel_id + kernel_row;
  uint32_t last_row = num_rows - KERNEL_SIZE + kernel_row + 1;

  // Assign queues
  queue_prev_x = queues_x[kernel_row][kernel_id * KERNEL_SIZE + 2];
  queue_prev_y = queues_y[kernel_row][kernel_id * KERNEL_SIZE + 2];
  queue_next_y = queues_row_acc[kernel_row][kernel_id];

  // Load weight
  weight = W[kernel_row * KERNEL_SIZE + 2];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = first_row; row < last_row; row += NUM_KERNELS) {
    // Populate kernel
    queue_pop(queue_prev_x, &curr_x);
    // Convolution
    for (uint32_t col = 1; col < num_cols - 1; ++col) {
      queue_pop(queue_prev_y, &curr_y);
      curr_y += curr_x * weight;
      queue_pop(queue_prev_x, &curr_x);
      queue_push(queue_next_y, curr_y, &resp_y);
    }
    // Flush kernel
    queue_pop(queue_prev_x, &curr_x);
  }
}

void systolic_conv_row_acc(const uint32_t kernel_id, const uint32_t num_rows_y,
                           const uint32_t num_cols_y, int32_t *__restrict__ Y) {
  int32_t *queue_y_0;
  int32_t *queue_y_1;
  int32_t *queue_y_2;
  int32_t curr_y_0;
  int32_t curr_y_1;
  int32_t curr_y_2;
  int32_t total_y;

  // Assign queues
  queue_y_0 = queues_row_acc[0][kernel_id];
  queue_y_1 = queues_row_acc[1][kernel_id];
  queue_y_2 = queues_row_acc[2][kernel_id];

  // Execute row-wise systolic 2d convolution
  for (uint32_t row = kernel_id; row < num_rows_y; row += NUM_KERNELS) {
    // Accumulate and Store
    for (uint32_t col = 0; col < num_cols_y; ++col) {
      queue_pop(queue_y_0, &curr_y_0);
      queue_pop(queue_y_1, &curr_y_1);
      queue_pop(queue_y_2, &curr_y_2);
      total_y = curr_y_0 + curr_y_1 + curr_y_2;
      Y[row * num_cols_y + col] = total_y;
    }
  }
}
