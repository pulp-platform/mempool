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
 * using central instruction based orchestration
 */

#include "alloc.h"
#include "printf.h"

// Size of systolic array
#define GRID_SIZE 4
#define SYSTOLIC_SIZE 3

// Size of all queues
#define QUEUE_SIZE 5

// Instruction Codes
#define INSTR_NOP 0
#define INSTR_RESET 1
#define INSTR_MATRIX_MUL 2
#define INSTR_END 3
#define INSTR_KILL 4

// Ceiling division function
#define CEIL_DIV(x, y) (x / y + (x % y != 0))

// Systolic matrix
typedef struct {
  int32_t **sub_matrices;
  uint32_t num_rows;
  uint32_t num_cols;
} systolic_matrix_t;

// TODO: SQRT ROOT OF NUM_CORES FOR GRID SIZE AND SYSTOLIC SIZE

// Array of queue ptrs in row-major order
queue_t *queues_down[GRID_SIZE - 1][GRID_SIZE];
queue_t *queues_right[GRID_SIZE][GRID_SIZE - 1];

void systolic_init() {
  for (uint32_t y = 0; y < GRID_SIZE - 1; ++y) {
    for (uint32_t x = 0; x < GRID_SIZE; ++x) {
      queue_create(&queues_down[y][x], QUEUE_SIZE);
    }
  }
  for (uint32_t y = 0; y < GRID_SIZE; ++y) {
    for (uint32_t x = 0; x < GRID_SIZE - 1; ++x) {
      queue_create(&queues_right[y][x], QUEUE_SIZE);
    }
  }
}

void systolic_matrix_allocate(systolic_matrix_t **syst_matrix,
                              uint32_t num_rows, uint32_t num_cols) {
  // Calculate how many submatrices in row and col dimension
  uint32_t syst_num_rows = CEIL_DIV(num_rows, SYSTOLIC_SIZE);
  uint32_t syst_num_cols = CEIL_DIV(num_cols, SYSTOLIC_SIZE);

  // Calculate size of submatrices
  uint32_t sub_matrix_size = SYSTOLIC_SIZE * SYSTOLIC_SIZE * 4;

  // Calculate number of submatrices
  uint32_t num_sub_matrices = syst_num_rows * syst_num_cols;

  // Allocate submatrices array
  int32_t **sub_matrices = (int32_t **)simple_malloc(num_sub_matrices * 4);

  // Allocate submatrices
  for (uint32_t i = 0; i < num_sub_matrices; ++i) {
    sub_matrices[i] = (int32_t *)simple_malloc(sub_matrix_size);
  }

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->sub_matrices = sub_matrices;
  new_matrix->num_rows = syst_num_rows;
  new_matrix->num_cols = syst_num_cols;

  *syst_matrix = new_matrix;
}

// TODO: Copy over for non-multiple matrices -> Fill with 0 (memory overflow)
void systolic_matrix_create(systolic_matrix_t **syst_matrix, int32_t *matrix,
                            uint32_t num_rows, uint32_t num_cols) {
  // Calculate how many submatrices in row and col dimension
  uint32_t syst_num_rows = CEIL_DIV(num_rows, SYSTOLIC_SIZE);
  uint32_t syst_num_cols = CEIL_DIV(num_cols, SYSTOLIC_SIZE);

  // Calculate size of submatrices
  uint32_t sub_matrix_size = SYSTOLIC_SIZE * SYSTOLIC_SIZE * 4;

  // Allocate submatrices array
  int32_t **sub_matrices =
      (int32_t **)simple_malloc(syst_num_rows * syst_num_cols * 4);

  // Store submatrices
  uint32_t idx = 0;
  uint32_t anchor;
  for (uint32_t y = 0; y < num_rows; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols; x += SYSTOLIC_SIZE) {
      // Allocate submatrix
      int32_t *sub_matrix = (int32_t *)simple_malloc(sub_matrix_size);

      // Copy over values from matrix
      anchor = y * num_cols + x;
      for (uint32_t syst_y = 0; syst_y < SYSTOLIC_SIZE; ++syst_y) {
        for (uint32_t syst_x = 0; syst_x < SYSTOLIC_SIZE; ++syst_x) {
          sub_matrix[syst_y * SYSTOLIC_SIZE + syst_x] =
              matrix[anchor + syst_y * num_cols + syst_x];
        }
      }

      // Add submatrix to array of submatrices
      sub_matrices[idx++] = sub_matrix;
    }
  }

  // Allocate systolic matrix
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(3 * 4);

  // Assign values to systolic matrix
  new_matrix->sub_matrices = sub_matrices;
  new_matrix->num_rows = syst_num_rows;
  new_matrix->num_cols = syst_num_cols;

  *syst_matrix = new_matrix;
}

void systolic_matrix_print(systolic_matrix_t *matrix) {
  printf("Systolic matrix at 0x%08X\n", (uint32_t)matrix);
  uint32_t num_syst_rows = matrix->num_rows;
  uint32_t num_syst_cols = matrix->num_cols;
  int32_t *sub_matrix;
  int32_t **sub_matrices = matrix->sub_matrices;
  for (uint32_t syst_y = 0; syst_y < num_syst_rows; ++syst_y) {
    for (uint32_t sub_y = 0; sub_y < SYSTOLIC_SIZE; ++sub_y) {
      for (uint32_t syst_x = 0; syst_x < num_syst_cols; ++syst_x) {
        sub_matrix = sub_matrices[syst_y * num_syst_cols + syst_x];
        for (uint32_t sub_x = 0; sub_x < SYSTOLIC_SIZE; ++sub_x) {
          printf("%5d ", sub_matrix[sub_y * SYSTOLIC_SIZE + sub_x]);
        }
      }
      printf("\n");
    }
  }
}

/* A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB (currently only support multiples of SYSTOLIC_SIZE?)
 * (max dimension is 16-bit)
 */
void systolic_matrix_mul(systolic_matrix_t const *__restrict__ A,
                         systolic_matrix_t const *__restrict__ B,
                         systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t instr;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t *arg_horz_ptr;
  int32_t *arg_vert_ptr;
  int32_t **sub_matrices_A;
  int32_t **sub_matrices_B;
  int32_t **sub_matrices_C;
  uint32_t num_cols_A;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;

  // Assign queues
  queue_next_horz = queues_right[0][0];
  queue_next_vert = queues_down[0][0];

  // Get array of submatrices
  sub_matrices_A = A->sub_matrices;
  sub_matrices_B = B->sub_matrices;
  sub_matrices_C = C->sub_matrices;

  // Get dimensions of submatrices
  num_cols_A = A->num_cols;
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Repetition count per sub_matrix_C (A->num_cols == B->num_rows)
  instr_rep = (uint16_t)num_cols_A;

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Reset instruction
      instr = INSTR_RESET;
      return_ptr = sub_matrices_C[y * num_cols_C + x];
      blocking_queue_push(queue_next_horz, &instr);
      blocking_queue_push(queue_next_horz, (int32_t *)&return_ptr);
      blocking_queue_push(queue_next_vert, &instr);
      blocking_queue_push(queue_next_vert, (int32_t *)&return_ptr);

      // Matrix multiplication instruction
      instr = (instr_rep << 16) | INSTR_MATRIX_MUL;
      return_ptr = sub_matrices_C[y * num_cols_C + x];
      blocking_queue_push(queue_next_horz, &instr);
      blocking_queue_push(queue_next_horz, (int32_t *)&return_ptr);
      blocking_queue_push(queue_next_vert, &instr);
      blocking_queue_push(queue_next_vert, (int32_t *)&return_ptr);

      // Push pointer to submatrices of A & B
      for (uint32_t i = 0; i < instr_rep; ++i) {
        arg_horz_ptr = sub_matrices_B[i * num_cols_B + x];
        arg_vert_ptr = sub_matrices_A[y * num_cols_A + i];
        blocking_queue_push(queue_next_horz, (int32_t *)&arg_horz_ptr);
        blocking_queue_push(queue_next_vert, (int32_t *)&arg_vert_ptr);
      }
    }
  }

  // End instruction
  instr = INSTR_END;
  return_ptr = (int32_t *)simple_malloc(4);
  *return_ptr = 0;
  blocking_queue_push(queue_next_horz, &instr);
  blocking_queue_push(queue_next_horz, (int32_t *)&return_ptr);
  blocking_queue_push(queue_next_vert, &instr);
  blocking_queue_push(queue_next_vert, (int32_t *)&return_ptr);

  // Wait for end flag
  while (return_ptr == 0) {
    mempool_wait(1);
  };
}

void systolic_kill_loop() {
  int32_t instr = INSTR_KILL;
  blocking_queue_push(queues_right[0][0], &instr);
  blocking_queue_push(queues_down[0][0], &instr);
}

void systolic_column_ctrl(const uint32_t idx) {
  uint8_t loop = 1;
  queue_t *queue_prev;
  queue_t *queue_next;
  queue_t *queue_data;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t *arg_ptr;

  // Assign queues
  queue_prev = queues_right[0][idx - 1];
  if (idx == GRID_SIZE - 1) {
    queue_next = NULL;
  } else {
    queue_next = queues_right[0][idx];
  }
  queue_data = queues_down[0][idx];

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    blocking_queue_pop(queue_prev, &instr);
    if (queue_next) {
      blocking_queue_push(queue_next, &instr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      blocking_queue_push(queue_data, &instr);
      break;

    case INSTR_RESET:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, (int32_t *)&return_ptr);
      break;

    case INSTR_MATRIX_MUL:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, (int32_t *)&return_ptr);
      for (uint32_t i = 0; i < instr_rep; ++i) {
        blocking_queue_pop(queue_prev, (int32_t *)&arg_ptr);
        if (queue_next) {
          blocking_queue_push(queue_next, (int32_t *)&arg_ptr);
        }
        uint32_t offset;
        for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
          offset = y * SYSTOLIC_SIZE + idx - 1;
          blocking_queue_push(queue_data, (arg_ptr + offset));
        }
      }
      break;

    case INSTR_END:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, (int32_t *)&return_ptr);
      break;

    case INSTR_KILL:
      blocking_queue_push(queue_data, &instr);
      loop = 0;
      break;

    default:
      printf("Invalid instruction at CC%02u\n", idx);
    }
  }
}

void systolic_row_ctrl(const uint32_t idx) {
  uint8_t loop = 1;
  queue_t *queue_prev;
  queue_t *queue_next;
  queue_t *queue_data;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t *arg_ptr;

  // Assign queues
  queue_prev = queues_down[idx - 1][0];
  if (idx == GRID_SIZE - 1) {
    queue_next = NULL;
  } else {
    queue_next = queues_down[idx][0];
  }
  queue_data = queues_right[idx][0];

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    blocking_queue_pop(queue_prev, &instr);
    if (queue_next) {
      blocking_queue_push(queue_next, &instr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      blocking_queue_push(queue_data, &instr);
      break;

    case INSTR_RESET:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, &instr);
      break;

    case INSTR_MATRIX_MUL:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, &instr);
      for (uint32_t i = 0; i < instr_rep; ++i) {
        blocking_queue_pop(queue_prev, (int32_t *)&arg_ptr);
        if (queue_next) {
          blocking_queue_push(queue_next, (int32_t *)&arg_ptr);
        }
        uint32_t offset;
        for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
          offset = (idx - 1) * SYSTOLIC_SIZE + x;
          blocking_queue_push(queue_data, (arg_ptr + offset));
        }
      }
      break;

    case INSTR_END:
      blocking_queue_pop(queue_prev, (int32_t *)&return_ptr);
      if (queue_next) {
        blocking_queue_push(queue_next, (int32_t *)&return_ptr);
      }
      blocking_queue_push(queue_data, &instr);
      break;

    case INSTR_KILL:
      blocking_queue_push(queue_data, &instr);
      loop = 0;
      break;

    default:
      printf("Invalid instruction at RC%02u\n", idx);
    }
  }
}

void systolic_proc_element(const uint32_t row_idx, const uint32_t col_idx) {
  uint8_t loop = 1;
  uint32_t data_row_idx = row_idx - 1;
  uint32_t data_col_idx = col_idx - 1;
  queue_t *queue_prev_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t instr;
  uint16_t instr_code;
  uint16_t instr_rep;
  int32_t *return_ptr;
  int32_t data_horz;
  int32_t data_vert;
  uint32_t offset;

  // Assign queues
  queue_prev_horz = queues_right[row_idx][col_idx - 1];
  queue_prev_vert = queues_down[row_idx - 1][col_idx];
  if (col_idx == GRID_SIZE - 1) {
    queue_next_horz = NULL;
  } else {
    queue_next_horz = queues_right[row_idx][col_idx];
  }
  if (row_idx == GRID_SIZE - 1) {
    queue_next_vert = NULL;
  } else {
    queue_next_vert = queues_down[row_idx][col_idx];
  }

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    blocking_queue_pop(queue_prev_horz, &instr);
    blocking_queue_pop(queue_prev_vert, (int32_t *)&return_ptr);
    if (queue_next_horz) {
      blocking_queue_push(queue_next_horz, &instr);
    }
    if (queue_next_vert) {
      blocking_queue_push(queue_next_vert, (int32_t *)&return_ptr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      break;

    case INSTR_RESET:
      offset = data_row_idx * SYSTOLIC_SIZE + data_col_idx;
      *(return_ptr + offset) = 0;
      break;

    case INSTR_MATRIX_MUL:
      for (uint32_t i = 0; i < instr_rep; ++i) {
        for (uint32_t k = 0; k < SYSTOLIC_SIZE; ++k) {
          blocking_queue_pop(queue_prev_horz, &data_horz);
          blocking_queue_pop(queue_prev_vert, &data_vert);
          offset = data_row_idx * SYSTOLIC_SIZE + data_col_idx;
          *(return_ptr + offset) += data_horz * data_vert;
          if (queue_next_horz) {
            blocking_queue_push(queue_next_horz, &data_horz);
          }
          if (queue_next_vert) {
            blocking_queue_push(queue_next_vert, &data_vert);
          }
        }
      }
      break;

    case INSTR_END:
      if ((row_idx == SYSTOLIC_SIZE) && (col_idx == SYSTOLIC_SIZE)) {
        *return_ptr = 1;
      }
      break;

    case INSTR_KILL:
      loop = 0;
      break;

    default:
      printf("Invalid instruction at PE(%02u,%02u)\n", row_idx, col_idx);
    }
  }
}
