// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

// Size of systolic array
#define SYSTOLIC_SIZE 4

// Size of all queues
#define QUEUE_SIZE 5

// Ceiling division function
#define CEIL_DIV(x, y) (x / y + (x % y != 0))

// Systolic matrix
typedef struct {
  int32_t **sub_matrices;
  uint32_t num_rows;
  uint32_t num_cols;
} systolic_matrix_t;

// Cycle counters for benchmark
uint32_t bm_h_pop_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_h_push_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_v_pop_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_v_push_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

// TODO: SQRT ROOT OF NUM_CORES FOR SYSTOLIC SIZE

// Array of queue ptrs in row-major order
queue_t *queues_vert[SYSTOLIC_SIZE - 1][SYSTOLIC_SIZE];
queue_t *queues_horz[SYSTOLIC_SIZE][SYSTOLIC_SIZE - 1];

void systolic_init(uint32_t const *grid_mapping) {
  uint32_t grid_pos = 0;
  alloc_t *alloc;
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      alloc = get_alloc_tile(grid_mapping[grid_pos]);
      if (y != SYSTOLIC_SIZE - 1) {
        queue_domain_create(alloc, &queues_vert[y][x], QUEUE_SIZE);
      }
      if (x != SYSTOLIC_SIZE - 1) {
        queue_domain_create(alloc, &queues_horz[y][x], QUEUE_SIZE);
      }
      ++grid_pos;
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
  printf("horz pop:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", bm_h_pop_cnt[y][x]);
    }
    printf("\n");
  }
  printf("horz push:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", bm_h_push_cnt[y][x]);
    }
    printf("\n");
  }
  printf("vert pop:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", bm_v_pop_cnt[y][x]);
    }
    printf("\n");
  }
  printf("vert push:\n");
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      printf("%5d ", bm_v_push_cnt[y][x]);
    }
    printf("\n");
  }
}

// row and column producing processing element
void systolic_rcp_pe(const uint32_t rep_count,
                     systolic_matrix_t const *__restrict__ A,
                     systolic_matrix_t const *__restrict__ B,
                     systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t data_horz;
  int32_t data_vert;
  int32_t **sub_matrices_A;
  int32_t **sub_matrices_B;
  int32_t **sub_matrices_C;
  uint32_t num_cols_A;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t data_offset;
  int32_t *curr_sub_matrix_A;
  int32_t *curr_sub_matrix_B;
  int32_t *curr_sub_matrix_C;
  int32_t *curr_element_C;
  uint32_t h_push_cnt = 0;
  uint32_t v_push_cnt = 0;

  // Assign queues
  queue_next_horz = queues_horz[0][0];
  queue_next_vert = queues_vert[0][0];

  // Get array of submatrices
  sub_matrices_A = A->sub_matrices;
  sub_matrices_B = B->sub_matrices;
  sub_matrices_C = C->sub_matrices;

  // Get dimensions of submatrices
  num_cols_A = A->num_cols;
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Set data offset depending on PE position
  data_offset = 0;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_push(queue_next_horz, &data_horz);
  blocking_queue_push(queue_next_vert, &data_vert);

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Set current submatrix C
      curr_sub_matrix_C = sub_matrices_C[y * num_cols_C + x];
      curr_element_C = curr_sub_matrix_C + data_offset;

      // Reset value
      *curr_element_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < rep_count; ++i) {
        curr_sub_matrix_A = sub_matrices_A[y * num_cols_A + i];
        curr_sub_matrix_B = sub_matrices_B[i * num_cols_B + x];
        for (uint32_t j = 0; j < SYSTOLIC_SIZE; ++j) {
          data_horz = *(curr_sub_matrix_A + data_offset + j);
          data_vert = *(curr_sub_matrix_B + data_offset + j * SYSTOLIC_SIZE);
          counting_queue_push(queue_next_horz, &data_horz, &h_push_cnt);
          counting_queue_push(queue_next_vert, &data_vert, &v_push_cnt);
          *curr_element_C += data_horz * data_vert;
        }
      }
    }
  }

  bm_h_push_cnt[0][0] = h_push_cnt;
  bm_v_push_cnt[0][0] = v_push_cnt;
}

// column producing processing element
void systolic_cp_pe(const uint32_t col_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ B,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_prev_horz;
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t data_horz;
  int32_t data_vert;
  int32_t **sub_matrices_B;
  int32_t **sub_matrices_C;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t data_offset;
  int32_t *curr_sub_matrix_B;
  int32_t *curr_sub_matrix_C;
  int32_t *curr_element_C;
  uint32_t h_pop_cnt = 0;
  uint32_t h_push_cnt = 0;
  uint32_t v_push_cnt = 0;

  // Assign queues
  queue_prev_horz = queues_horz[0][col_idx - 1];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    queue_next_horz = NULL;
  } else {
    queue_next_horz = queues_horz[0][col_idx];
  }
  queue_next_vert = queues_vert[0][col_idx];

  // Get array of submatrices
  sub_matrices_B = B->sub_matrices;
  sub_matrices_C = C->sub_matrices;

  // Get dimensions of submatrices
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Set data offset depending on PE position
  data_offset = col_idx;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_horz, &data_horz);
  if (queue_next_horz) {
    blocking_queue_push(queue_next_horz, &data_horz);
  }
  blocking_queue_push(queue_next_vert, &data_vert);

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Set current submatrix C
      curr_sub_matrix_C = sub_matrices_C[y * num_cols_C + x];
      curr_element_C = curr_sub_matrix_C + data_offset;

      // Reset value
      *curr_element_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < rep_count; ++i) {
        curr_sub_matrix_B = sub_matrices_B[i * num_cols_B + x];
        for (uint32_t j = 0; j < SYSTOLIC_SIZE; ++j) {
          data_vert = *(curr_sub_matrix_B + data_offset + j * SYSTOLIC_SIZE);
          counting_queue_pop(queue_prev_horz, &data_horz, &h_pop_cnt);
          if (queue_next_horz) {
            counting_queue_push(queue_next_horz, &data_horz, &h_push_cnt);
          }
          counting_queue_push(queue_next_vert, &data_vert, &v_push_cnt);
          *curr_element_C += data_horz * data_vert;
        }
      }
    }
  }

  bm_h_pop_cnt[0][col_idx] = h_pop_cnt;
  bm_h_push_cnt[0][col_idx] = h_push_cnt;
  bm_v_push_cnt[0][col_idx] = v_push_cnt;
}

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ A,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_next_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_vert;
  int32_t data_horz;
  int32_t data_vert;
  int32_t **sub_matrices_A;
  int32_t **sub_matrices_C;
  uint32_t num_cols_A;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t data_offset;
  int32_t *curr_sub_matrix_A;
  int32_t *curr_sub_matrix_C;
  int32_t *curr_element_C;
  uint32_t h_push_cnt = 0;
  uint32_t v_pop_cnt = 0;
  uint32_t v_push_cnt = 0;

  // Assign queues
  queue_next_horz = queues_horz[row_idx][0];
  queue_prev_vert = queues_vert[row_idx - 1][0];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    queue_next_vert = NULL;
  } else {
    queue_next_vert = queues_vert[row_idx][0];
  }

  // Get array of submatrices
  sub_matrices_A = A->sub_matrices;
  sub_matrices_C = C->sub_matrices;

  // Get dimensions of submatrices
  num_cols_A = A->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Set data offset depending on PE position
  data_offset = row_idx * SYSTOLIC_SIZE;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_vert, &data_vert);
  blocking_queue_push(queue_next_horz, &data_horz);
  if (queue_next_vert) {
    blocking_queue_push(queue_next_vert, &data_vert);
  }

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Set current submatrix C
      curr_sub_matrix_C = sub_matrices_C[y * num_cols_C + x];
      curr_element_C = curr_sub_matrix_C + data_offset;

      // Reset value
      *curr_element_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < rep_count; ++i) {
        curr_sub_matrix_A = sub_matrices_A[y * num_cols_A + i];
        for (uint32_t j = 0; j < SYSTOLIC_SIZE; ++j) {
          data_horz = *(curr_sub_matrix_A + data_offset + j);
          counting_queue_pop(queue_prev_vert, &data_vert, &v_pop_cnt);
          counting_queue_push(queue_next_horz, &data_horz, &h_push_cnt);
          if (queue_next_vert) {
            counting_queue_push(queue_next_vert, &data_vert, &v_push_cnt);
          }
          *curr_element_C += data_horz * data_vert;
        }
      }
    }
  }

  bm_h_push_cnt[row_idx][0] = h_push_cnt;
  bm_v_pop_cnt[row_idx][0] = v_pop_cnt;
  bm_v_push_cnt[row_idx][0] = v_push_cnt;
}

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_prev_horz;
  queue_t *queue_next_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_vert;
  int32_t data_horz;
  int32_t data_vert;
  int32_t **sub_matrices_C;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t data_offset;
  int32_t *curr_sub_matrix_C;
  int32_t *curr_element_C;
  uint32_t h_pop_cnt = 0;
  uint32_t h_push_cnt = 0;
  uint32_t v_pop_cnt = 0;
  uint32_t v_push_cnt = 0;

  // Assign queues
  queue_prev_horz = queues_horz[row_idx][col_idx - 1];
  if (col_idx == SYSTOLIC_SIZE - 1) {
    queue_next_horz = NULL;
  } else {
    queue_next_horz = queues_horz[row_idx][col_idx];
  }
  queue_prev_vert = queues_vert[row_idx - 1][col_idx];
  if (row_idx == SYSTOLIC_SIZE - 1) {
    queue_next_vert = NULL;
  } else {
    queue_next_vert = queues_vert[row_idx][col_idx];
  }

  // Get array of submatrices
  sub_matrices_C = C->sub_matrices;

  // Get dimensions of submatrices
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Set data offset depending on PE position
  data_offset = row_idx * SYSTOLIC_SIZE + col_idx;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_horz, &data_horz);
  blocking_queue_pop(queue_prev_vert, &data_vert);
  if (queue_next_horz) {
    blocking_queue_push(queue_next_horz, &data_horz);
  }
  if (queue_next_vert) {
    blocking_queue_push(queue_next_vert, &data_vert);
  }

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; ++y) {
    for (uint32_t x = 0; x < num_cols_C; ++x) {
      // Set current submatrix C
      curr_sub_matrix_C = sub_matrices_C[y * num_cols_C + x];
      curr_element_C = curr_sub_matrix_C + data_offset;

      // Reset value
      *curr_element_C = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < rep_count; ++i) {
        for (uint32_t j = 0; j < SYSTOLIC_SIZE; ++j) {
          counting_queue_pop(queue_prev_horz, &data_horz, &h_pop_cnt);
          counting_queue_pop(queue_prev_vert, &data_vert, &v_pop_cnt);
          if (queue_next_horz) {
            counting_queue_push(queue_next_horz, &data_horz, &h_push_cnt);
          }
          if (queue_next_vert) {
            counting_queue_push(queue_next_vert, &data_vert, &v_push_cnt);
          }
          *curr_element_C += data_horz * data_vert;
        }
      }
    }
  }

  bm_h_pop_cnt[row_idx][col_idx] = h_pop_cnt;
  bm_h_push_cnt[row_idx][col_idx] = h_push_cnt;
  bm_v_pop_cnt[row_idx][col_idx] = v_pop_cnt;
  bm_v_push_cnt[row_idx][col_idx] = v_push_cnt;
}
