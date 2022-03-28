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
#include "systolic/queue_multi.h"

// Dimensions of square systolic array
// TODO: SQRT ROOT OF NUM_CORES FOR SYSTOLIC SIZE
#define SYSTOLIC_SIZE 16

// IMPORTANT: DATA_SIZE of queue_multi.h must be set to 4

// Systolic matrix
typedef struct {
  int32_t *matrix;
  uint32_t num_rows;
  uint32_t num_cols;
} systolic_matrix_t;

// Cycle counters for benchmark
uint32_t bm_h_pop_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_h_push_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_v_pop_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
uint32_t bm_v_push_cnt[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

// Array of queue ptrs in row-major order
queue_t *queues_vert[SYSTOLIC_SIZE - 1][SYSTOLIC_SIZE];
queue_t *queues_horz[SYSTOLIC_SIZE][SYSTOLIC_SIZE - 1];

// Define dump functions via CSR writes
dump(horz_pop, 0x7D1);
dump(vert_pop, 0x7D2);
dump(horz_push, 0x7D3);
dump(vert_push, 0x7D4);

void systolic_init(uint32_t const *grid_mapping) {
  // Create systolic array via queues
  uint32_t grid_pos = 0;
  alloc_t *alloc;
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      alloc = get_alloc_tile(grid_mapping[grid_pos]);
      if (y != SYSTOLIC_SIZE - 1) {
        queue_domain_create(alloc, &queues_vert[y][x]);
      }
      if (x != SYSTOLIC_SIZE - 1) {
        queue_domain_create(alloc, &queues_horz[y][x]);
      }
      ++grid_pos;
      // Initialize counters
      bm_h_pop_cnt[y][x] = 0;
      bm_h_push_cnt[y][x] = 0;
      bm_v_pop_cnt[y][x] = 0;
      bm_v_push_cnt[y][x] = 0;
    }
  }
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
  int32_t data_horz[4];
  int32_t data_vert[4];
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
  uint32_t h_push_cnt = 0;
  uint32_t v_push_cnt = 0;

  // Assign queues
  queue_next_horz = queues_horz[0][0];
  queue_next_vert = queues_vert[0][0];

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_push(queue_next_horz, data_horz);
  blocking_queue_push(queue_next_vert, data_vert);

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
        data_horz[1] = matrix_A[y * num_cols_A + i + 1];
        data_horz[2] = matrix_A[(y + 1) * num_cols_A + i];
        data_horz[3] = matrix_A[(y + 1) * num_cols_A + i + 1];
        data_vert[0] = matrix_B[i * num_cols_B + x];
        data_vert[1] = matrix_B[i * num_cols_B + x + 1];
        data_vert[2] = matrix_B[(i + 1) * num_cols_B + x];
        data_vert[3] = matrix_B[(i + 1) * num_cols_B + x + 1];
        counting_queue_push(queue_next_horz, data_horz, &h_push_cnt);
        counting_queue_push(queue_next_vert, data_vert, &v_push_cnt);
        curr_element_0_C += data_horz[1] * data_vert[2];
        curr_element_1_C += data_horz[1] * data_vert[3];
        curr_element_2_C += data_horz[3] * data_vert[2];
        curr_element_3_C += data_horz[3] * data_vert[3];
        curr_element_0_C += data_horz[0] * data_vert[0];
        curr_element_1_C += data_horz[0] * data_vert[1];
        curr_element_2_C += data_horz[2] * data_vert[0];
        curr_element_3_C += data_horz[2] * data_vert[1];
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

  // Store benchmark results
  bm_h_push_cnt[0][0] = h_push_cnt;
  bm_v_push_cnt[0][0] = v_push_cnt;

  // Dump benchmark results
  dump_horz_push(h_push_cnt);
  dump_vert_push(v_push_cnt);
}

// column producing processing element
void systolic_cp_pe(const uint32_t col_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ B,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_prev_horz;
  queue_t *queue_next_horz;
  queue_t *queue_next_vert;
  int32_t data_horz[4];
  int32_t data_vert[4];
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

  // Get matrix arrays
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_horz, data_horz);
  if (queue_next_horz) {
    blocking_queue_push(queue_next_horz, data_horz);
  }
  blocking_queue_push(queue_next_vert, data_vert);

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
          data_vert[0] = matrix_B[i * num_cols_B + shifted_x];
          data_vert[1] = matrix_B[i * num_cols_B + shifted_x + 1];
          data_vert[2] = matrix_B[(i + 1) * num_cols_B + shifted_x];
          data_vert[3] = matrix_B[(i + 1) * num_cols_B + shifted_x + 1];
          counting_queue_pop(queue_prev_horz, data_horz, &h_pop_cnt);
          if (queue_next_horz) {
            counting_queue_push(queue_next_horz, data_horz, &h_push_cnt);
          }
          counting_queue_push(queue_next_vert, data_vert, &v_push_cnt);
          curr_element_0_C += data_horz[1] * data_vert[2];
          curr_element_1_C += data_horz[1] * data_vert[3];
          curr_element_2_C += data_horz[3] * data_vert[2];
          curr_element_3_C += data_horz[3] * data_vert[3];
          curr_element_0_C += data_horz[0] * data_vert[0];
          curr_element_1_C += data_horz[0] * data_vert[1];
          curr_element_2_C += data_horz[2] * data_vert[0];
          curr_element_3_C += data_horz[2] * data_vert[1];
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
          blocking_queue_pop(queue_prev_horz, data_horz);
          if (queue_next_horz) {
            blocking_queue_push(queue_next_horz, data_horz);
          }
          blocking_queue_push(queue_next_vert, data_vert);
        }
      }
    }
  }

  // Store benchmark results
  bm_h_pop_cnt[0][col_idx] = h_pop_cnt;
  bm_h_push_cnt[0][col_idx] = h_push_cnt;
  bm_v_push_cnt[0][col_idx] = v_push_cnt;

  // Dump benchmark results
  dump_horz_pop(h_pop_cnt);
  dump_horz_push(h_push_cnt);
  dump_vert_push(v_push_cnt);
}

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ A,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_next_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_vert;
  int32_t data_horz[4];
  int32_t data_vert[4];
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

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_vert, data_vert);
  blocking_queue_push(queue_next_horz, data_horz);
  if (queue_next_vert) {
    blocking_queue_push(queue_next_vert, data_vert);
  }

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
          data_horz[1] = matrix_A[shifted_y * num_cols_A + i + 1];
          data_horz[2] = matrix_A[(shifted_y + 1) * num_cols_A + i];
          data_horz[3] = matrix_A[(shifted_y + 1) * num_cols_A + i + 1];
          counting_queue_pop(queue_prev_vert, data_vert, &v_pop_cnt);
          counting_queue_push(queue_next_horz, data_horz, &h_push_cnt);
          if (queue_next_vert) {
            counting_queue_push(queue_next_vert, data_vert, &v_push_cnt);
          }
          curr_element_0_C += data_horz[1] * data_vert[2];
          curr_element_1_C += data_horz[1] * data_vert[3];
          curr_element_2_C += data_horz[3] * data_vert[2];
          curr_element_3_C += data_horz[3] * data_vert[3];
          curr_element_0_C += data_horz[0] * data_vert[0];
          curr_element_1_C += data_horz[0] * data_vert[1];
          curr_element_2_C += data_horz[2] * data_vert[0];
          curr_element_3_C += data_horz[2] * data_vert[1];
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
          blocking_queue_pop(queue_prev_vert, data_vert);
          blocking_queue_push(queue_next_horz, data_horz);
          if (queue_next_vert) {
            blocking_queue_push(queue_next_vert, data_vert);
          }
        }
      }
    }
  }

  // Store benchmark results
  bm_h_push_cnt[row_idx][0] = h_push_cnt;
  bm_v_pop_cnt[row_idx][0] = v_pop_cnt;
  bm_v_push_cnt[row_idx][0] = v_push_cnt;

  // Dump benchmark results
  dump_vert_pop(v_pop_cnt);
  dump_horz_push(h_push_cnt);
  dump_vert_push(v_push_cnt);
}

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ C) {
  queue_t *queue_prev_horz;
  queue_t *queue_next_horz;
  queue_t *queue_prev_vert;
  queue_t *queue_next_vert;
  int32_t data_horz[4];
  int32_t data_vert[4];
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

  // Get matrix arrays
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Start benchmark (remove initial latency from benchmark)
  // (we could use any data, data_* chosen arbitrarily)
  blocking_queue_pop(queue_prev_horz, data_horz);
  blocking_queue_pop(queue_prev_vert, data_vert);
  if (queue_next_horz) {
    blocking_queue_push(queue_next_horz, data_horz);
  }
  if (queue_next_vert) {
    blocking_queue_push(queue_next_vert, data_vert);
  }

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
          counting_queue_pop(queue_prev_horz, data_horz, &h_pop_cnt);
          counting_queue_pop(queue_prev_vert, data_vert, &v_pop_cnt);
          if (queue_next_horz) {
            counting_queue_push(queue_next_horz, data_horz, &h_push_cnt);
          }
          if (queue_next_vert) {
            counting_queue_push(queue_next_vert, data_vert, &v_push_cnt);
          }
          curr_element_0_C += data_horz[1] * data_vert[2];
          curr_element_1_C += data_horz[1] * data_vert[3];
          curr_element_2_C += data_horz[3] * data_vert[2];
          curr_element_3_C += data_horz[3] * data_vert[3];
          curr_element_0_C += data_horz[0] * data_vert[0];
          curr_element_1_C += data_horz[0] * data_vert[1];
          curr_element_2_C += data_horz[2] * data_vert[0];
          curr_element_3_C += data_horz[2] * data_vert[1];
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
          blocking_queue_pop(queue_prev_horz, data_horz);
          blocking_queue_pop(queue_prev_vert, data_vert);
          if (queue_next_horz) {
            blocking_queue_push(queue_next_horz, data_horz);
          }
          if (queue_next_vert) {
            blocking_queue_push(queue_next_vert, data_vert);
          }
        }
      }
    }
  }

  // Store benchmark results
  bm_h_pop_cnt[row_idx][col_idx] = h_pop_cnt;
  bm_h_push_cnt[row_idx][col_idx] = h_push_cnt;
  bm_v_pop_cnt[row_idx][col_idx] = v_pop_cnt;
  bm_v_push_cnt[row_idx][col_idx] = v_push_cnt;

  // Dump benchmark results
  dump_horz_pop(h_pop_cnt);
  dump_vert_pop(v_pop_cnt);
  dump_horz_push(h_push_cnt);
  dump_vert_push(v_push_cnt);
}
