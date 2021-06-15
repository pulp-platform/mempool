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

/* A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 * (max dimension is 16-bit)
 * Matrix is processed in 2x2 submatrices with the following indexing
 *
 *        B B          0 1
 *        B B          2 3
 *
 *   A A  C C  =  0 2  0 1
 *   A A  C C     1 3  2 3
 *
 * e.g. C0 = A2 * B2 + A0 * B0
 *
 * We use two interleaved queues per direction
 */

#include "alloc.h"
#include "printf.h"

// Dimensions of square systolic array
#define SYSTOLIC_SIZE 4

// Systolic matrix
typedef struct {
  int32_t *matrix;
  uint32_t num_rows;
  uint32_t num_cols;
} systolic_matrix_t;

// TODO: SQRT ROOT OF NUM_CORES FOR SYSTOLIC SIZE

// Array of queue ptrs in row-major order
int32_t *queues_vert_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_vert_1[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_1[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

// queue push
static inline void queue_push(void *const queue, int32_t data,
                              int32_t *const ret) {
  asm volatile("q.push.w %0, %1, (%2)" : "+r"(*ret) : "r"(data), "r"(queue));
}

// queue pop
inline void queue_pop(void *const queue, int32_t *const ret) {
  asm volatile("q.pop.w %0, 0(%1)" : "=r"(*ret) : "r"(queue));
}

void systolic_init(uint32_t const *tile_mapping, uint32_t const *core_mapping) {
  // Create systolic array via queues
  extern int32_t __seq_start;
  uint32_t grid_pos = 0;
  uint32_t tile_id;
  uint32_t core_id;
  uint32_t tile_offset;
  uint32_t core_offset;
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      tile_id = tile_mapping[grid_pos];
      core_id = core_mapping[grid_pos];
      tile_offset = tile_id * 4 * SEQ_MEM_SIZE / 4;
      core_offset = core_id % 4 * 4;
      queues_vert_0[y][x] = &__seq_start + tile_offset + core_offset + 0;
      queues_vert_1[y][x] = &__seq_start + tile_offset + core_offset + 1;
      queues_horz_0[y][x] = &__seq_start + tile_offset + core_offset + 2;
      queues_horz_1[y][x] = &__seq_start + tile_offset + core_offset + 3;
      ++grid_pos;
    }
  }

  // Print out queue addresses
  // printf("queues_vert_0\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_vert_0[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_vert_1\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_vert_1[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_horz_0\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_horz_0[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_horz_1\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_horz_1[y][x]);
  //   }
  //   printf("\n");
  // }
}

void systolic_matrix_allocate(systolic_matrix_t **syst_matrix,
                              uint32_t num_rows, uint32_t num_cols) {
  // Round up row and col dimension to next multiple of two
  uint32_t syst_num_rows = (uint32_t)((num_rows + 1) & 0xFFFE);
  uint32_t syst_num_cols = (uint32_t)((num_cols + 1) & 0xFFFE);

  // Allocate matrix array
  int32_t *array = (int32_t *)simple_malloc(syst_num_rows * syst_num_cols * 4);

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->matrix = array;
  new_matrix->num_rows = syst_num_rows;
  new_matrix->num_cols = syst_num_cols;

  *syst_matrix = new_matrix;
}

void systolic_matrix_create(systolic_matrix_t **syst_matrix, int32_t *matrix,
                            uint32_t num_rows, uint32_t num_cols) {
  // Round up row and col dimension to next multiple of two
  uint32_t syst_num_rows = (uint32_t)((num_rows + 1) & 0xFFFE);
  uint32_t syst_num_cols = (uint32_t)((num_cols + 1) & 0xFFFE);

  // Allocate matrix array
  int32_t *array = (int32_t *)simple_malloc(syst_num_rows * syst_num_cols * 4);

  // Copy data into new matrix array
  for (uint32_t y = 0; y < num_rows; ++y) {
    for (uint32_t x = 0; x < num_cols; ++x) {
      array[y * syst_num_cols + x] = matrix[y * num_cols + x];
    }
  }

  // Zero padding of matrix array
  if (syst_num_cols != num_cols) {
    for (uint32_t y = 0; y < syst_num_rows; ++y) {
      array[y * syst_num_cols + syst_num_cols - 1] = 0;
    }
  }
  if (syst_num_rows != num_rows) {
    for (uint32_t x = 0; x < syst_num_cols; ++x) {
      array[(syst_num_rows - 1) * syst_num_cols + x] = 0;
    }
  }

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->matrix = array;
  new_matrix->num_rows = syst_num_rows;
  new_matrix->num_cols = syst_num_cols;

  *syst_matrix = new_matrix;
}

void systolic_matrix_print(systolic_matrix_t *syst_matrix) {
  printf("Systolic matrix at 0x%08X\n", (uint32_t)syst_matrix);
  uint32_t num_rows = syst_matrix->num_rows;
  uint32_t num_cols = syst_matrix->num_cols;
  int32_t *matrix = syst_matrix->matrix;
  for (uint32_t y = 0; y < num_rows; ++y) {
    for (uint32_t x = 0; x < num_cols; ++x) {
      printf("%5d ", matrix[y * num_cols + x]);
    }
    printf("\n");
  }
}

// row and column producing processing element
void systolic_rcp_pe(const uint32_t rep_count,
                     systolic_matrix_t const *__restrict__ A,
                     systolic_matrix_t const *__restrict__ B,
                     systolic_matrix_t const *__restrict__ C) {
  int32_t *queue_next_horz_0;
  int32_t *queue_next_horz_1;
  int32_t *queue_next_vert_0;
  int32_t *queue_next_vert_1;
  int32_t data_horz[4] = {0, 0, 0, 0};
  int32_t data_vert[4] = {0, 0, 0, 0};
  int32_t resp_horz_0 __attribute__((unused)) = 0;
  int32_t resp_horz_1 __attribute__((unused)) = 0;
  int32_t resp_vert_0 __attribute__((unused)) = 0;
  int32_t resp_vert_1 __attribute__((unused)) = 0;
  int32_t *matrix_A;
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  int32_t curr_element_0_C;
  int32_t curr_element_1_C;
  int32_t curr_element_2_C;
  int32_t curr_element_3_C;
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;

  // Assign queues
  queue_next_horz_0 = queues_horz_0[0][1];
  queue_next_horz_1 = queues_horz_1[0][1];
  queue_next_vert_0 = queues_vert_0[1][0];
  queue_next_vert_1 = queues_vert_1[1][0];

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
      // Reset values
      curr_element_0_C = 0;
      curr_element_1_C = 0;
      curr_element_2_C = 0;
      curr_element_3_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
        data_horz[0] = matrix_A[y * num_cols_A + i];
        data_vert[0] = matrix_B[i * num_cols_B + x];
        data_horz[1] = matrix_A[(y + 1) * num_cols_A + i];
        data_vert[1] = matrix_B[i * num_cols_B + x + 1];
        queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
        queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
        queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
        queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
        curr_element_0_C += data_horz[0] * data_vert[0];
        curr_element_1_C += data_horz[0] * data_vert[1];
        curr_element_2_C += data_horz[1] * data_vert[0];
        curr_element_3_C += data_horz[1] * data_vert[1];
        data_horz[2] = matrix_A[y * num_cols_A + i + 1];
        data_vert[2] = matrix_B[(i + 1) * num_cols_B + x];
        data_horz[3] = matrix_A[(y + 1) * num_cols_A + i + 1];
        data_vert[3] = matrix_B[(i + 1) * num_cols_B + x + 1];
        queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
        queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
        queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
        queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
        curr_element_0_C += data_horz[2] * data_vert[2];
        curr_element_1_C += data_horz[2] * data_vert[3];
        curr_element_2_C += data_horz[3] * data_vert[2];
        curr_element_3_C += data_horz[3] * data_vert[3];
      }

      // Store values
      anchor_row_0 = y * num_cols_C + x;
      anchor_row_1 = anchor_row_0 + num_cols_C;
      matrix_C[anchor_row_0] = curr_element_0_C;
      matrix_C[anchor_row_0 + 1] = curr_element_1_C;
      matrix_C[anchor_row_1] = curr_element_2_C;
      matrix_C[anchor_row_1 + 1] = curr_element_3_C;
    }
  }
}

// column producing processing element
void systolic_cp_pe(const uint32_t col_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ B,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *queue_prev_horz_0;
  int32_t *queue_prev_horz_1;
  int32_t *queue_next_horz_0;
  int32_t *queue_next_horz_1;
  int32_t *queue_next_vert_0;
  int32_t *queue_next_vert_1;
  int32_t data_horz[4] = {0, 0, 0, 0};
  int32_t data_vert[4] = {0, 0, 0, 0};
  int32_t resp_horz_0 __attribute__((unused)) = 0;
  int32_t resp_horz_1 __attribute__((unused)) = 0;
  int32_t resp_vert_0 __attribute__((unused)) = 0;
  int32_t resp_vert_1 __attribute__((unused)) = 0;
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  int32_t curr_element_0_C;
  int32_t curr_element_1_C;
  int32_t curr_element_2_C;
  int32_t curr_element_3_C;
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;

  // Assign queues
  queue_prev_horz_0 = queues_horz_0[0][col_idx];
  queue_prev_horz_1 = queues_horz_1[0][col_idx];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    queue_next_horz_0 = NULL;
    queue_next_horz_1 = NULL;
  } else {
    queue_next_horz_0 = queues_horz_0[0][col_idx + 1];
    queue_next_horz_1 = queues_horz_1[0][col_idx + 1];
  }
  queue_next_vert_0 = queues_vert_0[1][col_idx];
  queue_next_vert_1 = queues_vert_1[1][col_idx];

  // Get matrix arrays
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Check if PE is at the right boundary
  if (queue_next_horz_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x
        shifted_x = x + 2 * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            data_vert[0] = matrix_B[i * num_cols_B + shifted_x];
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            data_vert[1] = matrix_B[i * num_cols_B + shifted_x + 1];
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            data_vert[2] = matrix_B[(i + 1) * num_cols_B + shifted_x];
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            data_vert[3] = matrix_B[(i + 1) * num_cols_B + shifted_x + 1];
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
          }
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x
        shifted_x = x + 2 * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            data_vert[0] = matrix_B[i * num_cols_B + shifted_x];
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            data_vert[1] = matrix_B[i * num_cols_B + shifted_x + 1];
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            data_vert[2] = matrix_B[(i + 1) * num_cols_B + shifted_x];
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            data_vert[3] = matrix_B[(i + 1) * num_cols_B + shifted_x + 1];
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_push(queue_next_vert_0, data_horz[0], &resp_vert_0);
            queue_push(queue_next_vert_1, data_horz[1], &resp_vert_1);
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_push(queue_next_vert_0, data_horz[2], &resp_vert_0);
            queue_push(queue_next_vert_1, data_horz[3], &resp_vert_1);
          }
        }
      }
    }
  }
}

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ A,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *queue_next_horz_0;
  int32_t *queue_next_horz_1;
  int32_t *queue_prev_vert_0;
  int32_t *queue_prev_vert_1;
  int32_t *queue_next_vert_0;
  int32_t *queue_next_vert_1;
  int32_t data_horz[4] = {0, 0, 0, 0};
  int32_t data_vert[4] = {0, 0, 0, 0};
  int32_t resp_horz_0 __attribute__((unused)) = 0;
  int32_t resp_horz_1 __attribute__((unused)) = 0;
  int32_t resp_vert_0 __attribute__((unused)) = 0;
  int32_t resp_vert_1 __attribute__((unused)) = 0;
  int32_t *matrix_A;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_y;
  int32_t curr_element_0_C;
  int32_t curr_element_1_C;
  int32_t curr_element_2_C;
  int32_t curr_element_3_C;
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;

  // Assign queues
  queue_next_horz_0 = queues_horz_0[row_idx][1];
  queue_next_horz_1 = queues_horz_1[row_idx][1];
  queue_prev_vert_0 = queues_vert_0[row_idx][0];
  queue_prev_vert_1 = queues_vert_1[row_idx][0];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    queue_next_vert_0 = NULL;
    queue_next_vert_1 = NULL;
  } else {
    queue_next_vert_0 = queues_vert_0[row_idx + 1][0];
    queue_next_vert_1 = queues_vert_1[row_idx + 1][0];
  }

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Check if PE is at the bottom boundary
  if (queue_next_vert_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            data_horz[0] = matrix_A[shifted_y * num_cols_A + i];
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            data_horz[1] = matrix_A[(shifted_y + 1) * num_cols_A + i];
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            data_horz[2] = matrix_A[shifted_y * num_cols_A + i + 1];
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            data_horz[3] = matrix_A[(shifted_y + 1) * num_cols_A + i + 1];
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
          }
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            data_horz[0] = matrix_A[shifted_y * num_cols_A + i];
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            data_horz[1] = matrix_A[(shifted_y + 1) * num_cols_A + i];
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            data_horz[2] = matrix_A[shifted_y * num_cols_A + i + 1];
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            data_horz[3] = matrix_A[(shifted_y + 1) * num_cols_A + i + 1];
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_vert[0], &resp_horz_0);
            queue_push(queue_next_horz_1, data_vert[1], &resp_horz_1);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_vert[2], &resp_horz_0);
            queue_push(queue_next_horz_1, data_vert[3], &resp_horz_1);
          }
        }
      }
    }
  }
}

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *queue_prev_horz_0;
  int32_t *queue_prev_horz_1;
  int32_t *queue_next_horz_0;
  int32_t *queue_next_horz_1;
  int32_t *queue_prev_vert_0;
  int32_t *queue_prev_vert_1;
  int32_t *queue_next_vert_0;
  int32_t *queue_next_vert_1;
  int32_t data_horz[4] = {0, 0, 0, 0};
  int32_t data_vert[4] = {0, 0, 0, 0};
  int32_t data_dummy __attribute__((unused)) = 0;
  int32_t resp_horz_0 __attribute__((unused)) = 0;
  int32_t resp_horz_1 __attribute__((unused)) = 0;
  int32_t resp_vert_0 __attribute__((unused)) = 0;
  int32_t resp_vert_1 __attribute__((unused)) = 0;
  int32_t *matrix_C;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  uint32_t shifted_y;
  int32_t curr_element_0_C;
  int32_t curr_element_1_C;
  int32_t curr_element_2_C;
  int32_t curr_element_3_C;
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;

  // Assign queues
  queue_prev_horz_0 = queues_horz_0[row_idx][col_idx];
  queue_prev_horz_1 = queues_horz_1[row_idx][col_idx];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    queue_next_horz_0 = NULL;
    queue_next_horz_1 = NULL;
  } else {
    queue_next_horz_0 = queues_horz_0[row_idx][col_idx + 1];
    queue_next_horz_1 = queues_horz_1[row_idx][col_idx + 1];
  }
  queue_prev_vert_0 = queues_vert_0[row_idx][col_idx];
  queue_prev_vert_1 = queues_vert_1[row_idx][col_idx];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    queue_next_vert_0 = NULL;
    queue_next_vert_1 = NULL;
  } else {
    queue_next_vert_0 = queues_vert_0[row_idx + 1][col_idx];
    queue_next_vert_1 = queues_vert_1[row_idx + 1][col_idx];
  }

  // Get matrix arrays
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // PE is not at a boundary
  if (queue_next_horz_0 && queue_next_vert_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
          }
        }
      }
    }
  }

  // PE is at the right boundary
  if (!queue_next_horz_0 && queue_next_vert_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            data_vert[0] += data_horz[0];
            data_vert[1] += data_horz[1];
            queue_push(queue_next_vert_0, data_vert[0], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[1], &resp_vert_1);
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            data_vert[2] += data_horz[2];
            data_vert[3] += data_horz[3];
            queue_push(queue_next_vert_0, data_vert[2], &resp_vert_0);
            queue_push(queue_next_vert_1, data_vert[3], &resp_vert_1);
          }
        }
      }
    }
  }

  // PE is at the bottom boundary
  if (queue_next_horz_0 && !queue_next_vert_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            data_horz[0] += data_vert[0];
            data_horz[1] += data_vert[1];
            queue_push(queue_next_horz_0, data_horz[0], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[1], &resp_horz_1);
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            data_horz[2] += data_vert[2];
            data_horz[3] += data_vert[3];
            queue_push(queue_next_horz_0, data_horz[2], &resp_horz_0);
            queue_push(queue_next_horz_1, data_horz[3], &resp_horz_1);
          }
        }
      }
    }
  }

  // PE is at the bottom right corner
  if (!queue_next_horz_0 && !queue_next_vert_0) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          // Reset values
          curr_element_0_C = 0;
          curr_element_1_C = 0;
          curr_element_2_C = 0;
          curr_element_3_C = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            curr_element_0_C += data_horz[0] * data_vert[0];
            curr_element_1_C += data_horz[0] * data_vert[1];
            curr_element_2_C += data_horz[1] * data_vert[0];
            curr_element_3_C += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            curr_element_0_C += data_horz[2] * data_vert[2];
            curr_element_1_C += data_horz[2] * data_vert[3];
            curr_element_2_C += data_horz[3] * data_vert[2];
            curr_element_3_C += data_horz[3] * data_vert[3];
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_element_0_C;
          matrix_C[anchor_row_0 + 1] = curr_element_1_C;
          matrix_C[anchor_row_1] = curr_element_2_C;
          matrix_C[anchor_row_1 + 1] = curr_element_3_C;
        } else {
          // Pop and push dummy data
          for (uint32_t i = 0; i < rep_count; ++i) {
            queue_pop(queue_prev_horz_0, &data_horz[0]);
            queue_pop(queue_prev_vert_0, &data_vert[0]);
            queue_pop(queue_prev_horz_1, &data_horz[1]);
            queue_pop(queue_prev_vert_1, &data_vert[1]);
            data_dummy += data_horz[0] * data_vert[0];
            data_dummy += data_horz[1] * data_vert[1];
            queue_pop(queue_prev_horz_0, &data_horz[2]);
            queue_pop(queue_prev_vert_0, &data_vert[2]);
            queue_pop(queue_prev_horz_1, &data_horz[3]);
            queue_pop(queue_prev_vert_1, &data_vert[3]);
            data_dummy += data_horz[2] * data_vert[2];
            data_dummy += data_horz[3] * data_vert[3];
            // TODO: FIND SAFER WAY TO ENFORCE DATA DEPENDENCY
            if (!data_dummy)
              break;
          }
        }
      }
    }
  }
}
