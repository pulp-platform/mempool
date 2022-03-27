// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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
#define INSTR_BM_START 5
#define INSTR_BM_END 6

// Ceiling division function
#define CEIL_DIV(x, y) (x / y + (x % y != 0))

// Systolic matrix
typedef struct {
  int32_t **sub_matrices;
  uint32_t num_rows;
  uint32_t num_cols;
} systolic_matrix_t;

// Cycle counters for benchmark
uint32_t cc_prev_pop_cntr[SYSTOLIC_SIZE];
uint32_t cc_next_push_cntr[SYSTOLIC_SIZE];
uint32_t cc_data_push_cntr[SYSTOLIC_SIZE];
uint32_t rc_prev_pop_cntr[SYSTOLIC_SIZE];
uint32_t rc_next_push_cntr[SYSTOLIC_SIZE];
uint32_t rc_data_push_cntr[SYSTOLIC_SIZE];
uint32_t pe_horz_pop_cntr[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t pe_horz_push_cntr[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t pe_vert_pop_cntr[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t pe_vert_push_cntr[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

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
  uint32_t rem_x, rem_y;
  for (uint32_t y = 0; y < num_rows; y += SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols; x += SYSTOLIC_SIZE) {
      // Allocate submatrix
      int32_t *sub_matrix = (int32_t *)simple_malloc(sub_matrix_size);

      // Copy over values from matrix
      anchor = y * num_cols + x;
      rem_x = num_cols - x;
      rem_y = num_rows - y;
      if ((rem_x < SYSTOLIC_SIZE) || (rem_y < SYSTOLIC_SIZE)) {
        // Submatrix is only partly within original matrix
        for (uint32_t sub_y = 0; sub_y < SYSTOLIC_SIZE; ++sub_y) {
          for (uint32_t sub_x = 0; sub_x < SYSTOLIC_SIZE; ++sub_x) {
            if ((sub_x < rem_x) && (sub_y < rem_y)) {
              sub_matrix[sub_y * SYSTOLIC_SIZE + sub_x] =
                  matrix[anchor + sub_y * num_cols + sub_x];
            } else {
              sub_matrix[sub_y * SYSTOLIC_SIZE + sub_x] = 0;
            }
          }
        }
      } else {
        // Submatrix is fully within original matrix
        for (uint32_t sub_y = 0; sub_y < SYSTOLIC_SIZE; ++sub_y) {
          for (uint32_t sub_x = 0; sub_x < SYSTOLIC_SIZE; ++sub_x) {
            sub_matrix[sub_y * SYSTOLIC_SIZE + sub_x] =
                matrix[anchor + sub_y * num_cols + sub_x];
          }
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

void systolic_benchmark_print() {
  printf("Benchmark: Cycles blocked by queue\n");
  printf("CC prev pop:  ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", cc_prev_pop_cntr[i]);
  }
  printf("\n");
  printf("CC next push: ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", cc_next_push_cntr[i]);
  }
  printf("\n");
  printf("CC data push: ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", cc_data_push_cntr[i]);
  }
  printf("\n");
  printf("RC prev pop:  ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", rc_prev_pop_cntr[i]);
  }
  printf("\n");
  printf("RC next push: ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", rc_next_push_cntr[i]);
  }
  printf("\n");
  printf("RC data push: ");
  for (uint32_t i = 0; i < SYSTOLIC_SIZE; ++i) {
    printf("%5d ", rc_data_push_cntr[i]);
  }
  printf("\n");
  printf("PE horz pop:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", pe_horz_pop_cntr[y][x]);
    }
    printf("\n");
  }
  printf("PE horz push:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", pe_horz_push_cntr[y][x]);
    }
    printf("\n");
  }
  printf("PE vert pop:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", pe_vert_pop_cntr[y][x]);
    }
    printf("\n");
  }
  printf("PE vert push:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", pe_vert_push_cntr[y][x]);
    }
    printf("\n");
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
  int32_t *return_addr;
  int32_t *arg_horz_addr;
  int32_t *arg_vert_addr;
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

  // Set addresses of pointers
  return_addr = (int32_t *)&return_ptr;
  arg_horz_addr = (int32_t *)&arg_horz_ptr;
  arg_vert_addr = (int32_t *)&arg_vert_ptr;

  // Start benchmark instruction
  instr = INSTR_BM_START;
  blocking_queue_push(queue_next_horz, &instr);
  blocking_queue_push(queue_next_vert, &instr);

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Reset instruction
      instr = INSTR_RESET;
      return_ptr = sub_matrices_C[y * num_cols_C + x];
      blocking_queue_push(queue_next_horz, &instr);
      blocking_queue_push(queue_next_horz, return_addr);
      blocking_queue_push(queue_next_vert, &instr);
      blocking_queue_push(queue_next_vert, return_addr);

      // Matrix multiplication instruction
      instr = (instr_rep << 16) | INSTR_MATRIX_MUL;
      return_ptr = sub_matrices_C[y * num_cols_C + x];
      blocking_queue_push(queue_next_horz, &instr);
      blocking_queue_push(queue_next_horz, return_addr);
      blocking_queue_push(queue_next_vert, &instr);
      blocking_queue_push(queue_next_vert, return_addr);

      // Push pointer to submatrices of A & B
      for (uint32_t i = 0; i < instr_rep; ++i) {
        arg_horz_ptr = sub_matrices_B[i * num_cols_B + x];
        arg_vert_ptr = sub_matrices_A[y * num_cols_A + i];
        blocking_queue_push(queue_next_horz, arg_horz_addr);
        blocking_queue_push(queue_next_vert, arg_vert_addr);
      }
    }
  }

  // End instruction
  instr = INSTR_END;
  return_ptr = (int32_t *)simple_malloc(4);
  *return_ptr = 0;
  blocking_queue_push(queue_next_horz, &instr);
  blocking_queue_push(queue_next_horz, return_addr);
  blocking_queue_push(queue_next_vert, &instr);
  blocking_queue_push(queue_next_vert, return_addr);

  // End benchmark instruction
  instr = INSTR_BM_END;
  blocking_queue_push(queue_next_horz, &instr);
  blocking_queue_push(queue_next_vert, &instr);

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
  int32_t *return_addr;
  int32_t *arg_addr;
  uint32_t prev_pop_cntr = 0;
  uint32_t next_push_cntr = 0;
  uint32_t data_push_cntr = 0;

  // Assign queues
  queue_prev = queues_right[0][idx - 1];
  if (idx == GRID_SIZE - 1) {
    queue_next = NULL;
  } else {
    queue_next = queues_right[0][idx];
  }
  queue_data = queues_down[0][idx];

  // Set addresses of pointers
  return_addr = (int32_t *)&return_ptr;
  arg_addr = (int32_t *)&arg_ptr;

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    counting_queue_pop(queue_prev, &instr, &prev_pop_cntr);
    if (queue_next) {
      counting_queue_push(queue_next, &instr, &next_push_cntr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      break;

    case INSTR_RESET:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, return_addr, &data_push_cntr);
      break;

    case INSTR_MATRIX_MUL:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, return_addr, &data_push_cntr);
      for (uint32_t i = 0; i < instr_rep; ++i) {
        counting_queue_pop(queue_prev, arg_addr, &prev_pop_cntr);
        if (queue_next) {
          counting_queue_push(queue_next, arg_addr, &next_push_cntr);
        }
        uint32_t offset;
        for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
          offset = y * SYSTOLIC_SIZE + idx - 1;
          counting_queue_push(queue_data, (arg_ptr + offset), &data_push_cntr);
        }
      }
      break;

    case INSTR_END:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, return_addr, &data_push_cntr);
      break;

    case INSTR_KILL:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      loop = 0;
      break;

    case INSTR_BM_START:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      prev_pop_cntr = 0;
      next_push_cntr = 0;
      data_push_cntr = 0;
      break;

    case INSTR_BM_END:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      cc_prev_pop_cntr[idx - 1] = prev_pop_cntr;
      cc_next_push_cntr[idx - 1] = next_push_cntr;
      cc_data_push_cntr[idx - 1] = data_push_cntr;
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
  int32_t *return_addr;
  int32_t *arg_addr;
  uint32_t prev_pop_cntr = 0;
  uint32_t next_push_cntr = 0;
  uint32_t data_push_cntr = 0;

  // Assign queues
  queue_prev = queues_down[idx - 1][0];
  if (idx == GRID_SIZE - 1) {
    queue_next = NULL;
  } else {
    queue_next = queues_down[idx][0];
  }
  queue_data = queues_right[idx][0];

  // Set addresses of pointers
  return_addr = (int32_t *)&return_ptr;
  arg_addr = (int32_t *)&arg_ptr;

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    counting_queue_pop(queue_prev, &instr, &prev_pop_cntr);
    if (queue_next) {
      counting_queue_push(queue_next, &instr, &next_push_cntr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      break;

    case INSTR_RESET:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      break;

    case INSTR_MATRIX_MUL:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      for (uint32_t i = 0; i < instr_rep; ++i) {
        counting_queue_pop(queue_prev, arg_addr, &prev_pop_cntr);
        if (queue_next) {
          counting_queue_push(queue_next, arg_addr, &next_push_cntr);
        }
        uint32_t offset;
        for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
          offset = (idx - 1) * SYSTOLIC_SIZE + x;
          counting_queue_push(queue_data, (arg_ptr + offset), &data_push_cntr);
        }
      }
      break;

    case INSTR_END:
      counting_queue_pop(queue_prev, return_addr, &prev_pop_cntr);
      if (queue_next) {
        counting_queue_push(queue_next, return_addr, &next_push_cntr);
      }
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      break;

    case INSTR_KILL:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      loop = 0;
      break;

    case INSTR_BM_START:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      prev_pop_cntr = 0;
      next_push_cntr = 0;
      data_push_cntr = 0;
      break;

    case INSTR_BM_END:
      counting_queue_push(queue_data, &instr, &data_push_cntr);
      rc_prev_pop_cntr[idx - 1] = prev_pop_cntr;
      rc_next_push_cntr[idx - 1] = next_push_cntr;
      rc_data_push_cntr[idx - 1] = data_push_cntr;
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
  int32_t *return_addr;
  int32_t data_horz;
  int32_t data_vert;
  uint32_t offset = data_row_idx * SYSTOLIC_SIZE + data_col_idx;
  uint32_t horz_pop_cntr = 0;
  uint32_t horz_push_cntr = 0;
  uint32_t vert_pop_cntr = 0;
  uint32_t vert_push_cntr = 0;

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

  // Set addresses of pointers
  return_addr = (int32_t *)&return_ptr;

  // Systolic loop
  while (loop) {
    // Receive instruction and instr_repetition count
    counting_queue_pop(queue_prev_horz, &instr, &horz_pop_cntr);
    counting_queue_pop(queue_prev_vert, return_addr, &vert_pop_cntr);
    if (queue_next_horz) {
      counting_queue_push(queue_next_horz, &instr, &horz_push_cntr);
    }
    if (queue_next_vert) {
      counting_queue_push(queue_next_vert, return_addr, &vert_push_cntr);
    }
    instr_rep = (uint16_t)(instr >> 16);
    instr_code = instr & 0xFFFF;

    switch (instr_code) {
    case INSTR_NOP:
      break;

    case INSTR_RESET:
      *(return_ptr + offset) = 0;
      break;

    case INSTR_MATRIX_MUL:
      for (uint32_t i = 0; i < instr_rep; ++i) {
        for (uint32_t k = 0; k < SYSTOLIC_SIZE; ++k) {
          counting_queue_pop(queue_prev_horz, &data_horz, &horz_pop_cntr);
          counting_queue_pop(queue_prev_vert, &data_vert, &vert_pop_cntr);
          if (queue_next_horz) {
            counting_queue_push(queue_next_horz, &data_horz, &horz_push_cntr);
          }
          if (queue_next_vert) {
            counting_queue_push(queue_next_vert, &data_vert, &vert_push_cntr);
          }
          *(return_ptr + offset) += data_horz * data_vert;
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

    case INSTR_BM_START:
      horz_pop_cntr = 0;
      horz_push_cntr = 0;
      vert_pop_cntr = 0;
      vert_push_cntr = 0;
      break;

    case INSTR_BM_END:
      pe_horz_pop_cntr[row_idx - 1][col_idx - 1] = horz_pop_cntr;
      pe_horz_push_cntr[row_idx - 1][col_idx - 1] = horz_push_cntr;
      pe_vert_pop_cntr[row_idx - 1][col_idx - 1] = vert_pop_cntr;
      pe_vert_push_cntr[row_idx - 1][col_idx - 1] = vert_push_cntr;
      break;

    default:
      printf("Invalid instruction at PE(%02u,%02u)\n", row_idx, col_idx);
    }
  }
}
