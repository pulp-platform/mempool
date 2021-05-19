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
int32_t *queues_vert[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

// TODO: GENERALIZE FOR ANY NUMBER OF TILES
void systolic_init(uint32_t const *grid_mapping) {
  // Create systolic array via queues
  extern int32_t __seq_start;
  uint32_t grid_pos = 0;
  uint32_t tile_id;
  uint32_t tile_offset;
  uint32_t bank_sel[4] = {0, 0, 0, 0};
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      tile_id = grid_mapping[grid_pos];
      tile_offset = tile_id * 4 * SEQ_MEM_SIZE / 4;
      queues_vert[y][x] = &__seq_start + tile_offset + bank_sel[tile_id];
      queues_horz[y][x] = &__seq_start + tile_offset + bank_sel[tile_id] + 1;
      bank_sel[tile_id] += 2;
      ++grid_pos;
    }
  }
  // TODO: PRINT OUT THE ADDRESSES TO CHECK
}

void systolic_matrix_allocate(systolic_matrix_t **syst_matrix,
                              uint32_t num_rows, uint32_t num_cols) {
  // Allocate matrix array
  int32_t *array = (int32_t *)simple_malloc(num_rows * num_cols * 4);

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->matrix = array;
  new_matrix->num_rows = num_rows;
  new_matrix->num_cols = num_cols;

  *syst_matrix = new_matrix;
}

void systolic_matrix_create(systolic_matrix_t **syst_matrix, int32_t *matrix,
                            uint32_t num_rows, uint32_t num_cols) {
  // Allocate matrix array
  int32_t *array = (int32_t *)simple_malloc(num_rows * num_cols * 4);

  // Copy data into new matrix array
  for (uint32_t y = 0; y < num_rows; ++y) {
    for (uint32_t x = 0; x < num_cols; ++x) {
      array[y * num_cols + x] = matrix[y * num_cols + x];
    }
  }

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->matrix = array;
  new_matrix->num_rows = num_rows;
  new_matrix->num_cols = num_cols;

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
  int32_t *q_next_horz;
  int32_t *q_next_vert;
  int32_t data_horz = 0;
  int32_t data_vert = 0;
  int32_t *matrix_A;
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  int32_t curr_element_C;

  // Assign queues
  q_next_horz = queues_horz[0][1];
  q_next_vert = queues_vert[1][0];

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
  for (uint32_t y = 0; y < num_rows_C; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += SYSTOLIC_SIZE) {
      // Reset value
      curr_element_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < rep_count; ++i) {
        data_horz = matrix_A[y * num_cols_A + i];
        data_vert = matrix_B[i * num_cols_B + x];
        __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
        __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
        curr_element_C += data_horz * data_vert;
      }

      // Store value
      matrix_C[y * num_cols_C + x] = curr_element_C;
    }
  }
}

// column producing processing element
void systolic_cp_pe(const uint32_t col_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ B,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *q_prev_horz;
  int32_t *q_next_horz;
  int32_t *q_next_vert;
  int32_t data_horz = 0;
  int32_t data_vert = 0;
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  int32_t curr_element_C;

  // Assign queues
  q_prev_horz = queues_horz[0][col_idx];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    q_next_horz = NULL;
  } else {
    q_next_horz = queues_horz[0][col_idx + 1];
  }
  q_next_vert = queues_vert[1][col_idx];

  // Get matrix arrays
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += SYSTOLIC_SIZE) {
      // Shift x
      shifted_x = x + col_idx;

      // Check if this PE is currently within the matrix C
      if (shifted_x < num_cols_C) {
        // Reset value
        curr_element_C = 0;

        // Systolic matrix multiplication through MACs
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_vert = matrix_B[i * num_cols_B + shifted_x];
          data_horz = __atomic_fetch_or(q_prev_horz, 0, __ATOMIC_SEQ_CST);
          if (q_next_horz) {
            __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
          }
          __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
          curr_element_C += data_horz * data_vert;
        }

        // Store value
        matrix_C[y * num_cols_C + shifted_x] = curr_element_C;
      } else {
        // Pop and push dummy data
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_horz = __atomic_fetch_or(q_prev_horz, 0, __ATOMIC_SEQ_CST);
          if (q_next_horz) {
            __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
          }
          __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
        }
      }
    }
  }
}

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ A,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *q_next_horz;
  int32_t *q_prev_vert;
  int32_t *q_next_vert;
  int32_t data_horz = 0;
  int32_t data_vert = 0;
  int32_t *matrix_A;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_y;
  int32_t curr_element_C;

  // Assign queues
  q_next_horz = queues_horz[row_idx][1];
  q_prev_vert = queues_vert[row_idx][0];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    q_next_vert = NULL;
  } else {
    q_next_vert = queues_vert[row_idx + 1][0];
  }

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += SYSTOLIC_SIZE) {
      // Shift y
      shifted_y = y + row_idx;

      // Check if this PE is currently within the matrix C
      if (shifted_y < num_rows_C) {
        // Reset value
        curr_element_C = 0;

        // Systolic matrix multiplication through MACs
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_horz = matrix_A[shifted_y * num_cols_A + i];
          data_vert = __atomic_fetch_or(q_prev_vert, 0, __ATOMIC_SEQ_CST);
          __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
          if (q_next_vert) {
            __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
          }
          curr_element_C += data_horz * data_vert;
        }

        // Store value
        matrix_C[shifted_y * num_cols_C + x] = curr_element_C;
      } else {
        // Pop and push dummy data
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_vert = __atomic_fetch_or(q_prev_vert, 0, __ATOMIC_SEQ_CST);
          __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
          if (q_next_vert) {
            __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
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
  int32_t *q_prev_horz;
  int32_t *q_next_horz;
  int32_t *q_prev_vert;
  int32_t *q_next_vert;
  int32_t data_horz = 0;
  int32_t data_vert = 0;
  int32_t *matrix_C;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  uint32_t shifted_y;
  int32_t curr_element_C;

  // Assign queues
  q_prev_horz = queues_horz[row_idx][col_idx];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    q_next_horz = NULL;
  } else {
    q_next_horz = queues_horz[row_idx][col_idx + 1];
  }
  q_prev_vert = queues_vert[row_idx][col_idx];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    q_next_vert = NULL;
  } else {
    q_next_vert = queues_vert[row_idx + 1][col_idx];
  }

  // Get matrix arrays
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += SYSTOLIC_SIZE) {
      // Shift x and y
      shifted_x = x + col_idx;
      shifted_y = y + row_idx;

      // Check if this PE is currently within the matrix C
      if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
        // Reset value
        curr_element_C = 0;

        // Systolic matrix multiplication through MACs
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_horz = __atomic_fetch_or(q_prev_horz, 0, __ATOMIC_SEQ_CST);
          data_vert = __atomic_fetch_or(q_prev_vert, 0, __ATOMIC_SEQ_CST);
          if (q_next_horz) {
            __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);
          }
          if (q_next_vert) {
            __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
          }
          curr_element_C += data_horz * data_vert;
        }

        // Store values
        matrix_C[shifted_y * num_cols_C + shifted_x] = curr_element_C;
      } else {
        // Pop and push dummy data
        for (uint32_t i = 0; i < rep_count; ++i) {
          data_horz = __atomic_fetch_or(q_prev_horz, 0, __ATOMIC_SEQ_CST);
          data_vert = __atomic_fetch_or(q_prev_vert, 0, __ATOMIC_SEQ_CST);
          if (q_next_horz) {
            __atomic_fetch_and(q_next_horz, data_horz, __ATOMIC_SEQ_CST);

          }
          if (q_next_vert) {
            __atomic_fetch_and(q_next_vert, data_vert, __ATOMIC_SEQ_CST);
          }
        }
      }
    }
  }
}
