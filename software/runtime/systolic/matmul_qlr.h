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
 * We use two interleaved queues per direction with following QLRs
 *
 *       t2 t3
 *
 *   t0  C0 C1
 *   t1  C2 C3
 */

#include "alloc.h"
#include "printf.h"

// Dimensions of square systolic array
#define SYSTOLIC_SIZE 4

// QLR configuration
#define QLR_CFG_T0 (QLR_CFG_BASE | (5 << 5))
#define QLR_CFG_T1 (QLR_CFG_BASE | (6 << 5))
#define QLR_CFG_T2 (QLR_CFG_BASE | (7 << 5))
#define QLR_CFG_T3 (QLR_CFG_BASE | (28 << 5))
#define QLR_CFG_TYPE 0
#define QLR_CFG_REQ 2
#define QLR_CFG_RF 3
#define QLR_CFG_IADDR 4
#define QLR_CFG_OADDR 5

// QLRs
register int32_t qlr_t0 asm("t0");
register int32_t qlr_t1 asm("t1");
register int32_t qlr_t2 asm("t2");
register int32_t qlr_t3 asm("t3");

// Systolic matrix (TODO: remove systolic matrix and limit to even matrices)
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

void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t grid_pos = 0;
  uint32_t core_id;
  uint32_t offset;
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      core_id = core_map[grid_pos];
      offset = core_id * 4;
      queues_vert_0[y][x] = (int32_t *)(offset + 0);
      queues_vert_1[y][x] = (int32_t *)(offset + 1);
      queues_horz_0[y][x] = (int32_t *)(offset + 2);
      queues_horz_1[y][x] = (int32_t *)(offset + 3);
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
  int32_t *array = (int32_t *)simple_malloc(syst_num_rows * syst_num_cols * sizeof(int32_t));

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
  systolic_matrix_t *new_matrix = (systolic_matrix_t *)simple_malloc(sizeof(systolic_matrix_t));

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
  int32_t *matrix_A;
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  register int32_t curr_C[4];
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
  qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][1];
  qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
  qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][1];
  qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
  qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][0];
  qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
  qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_1[1][0];

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
      write_csr(0, x);
      write_csr(1, y);
      // Start QLRs
      qlr_cfg_t0[QLR_CFG_TYPE] = 2;
      qlr_cfg_t1[QLR_CFG_TYPE] = 2;
      qlr_cfg_t2[QLR_CFG_TYPE] = 2;
      qlr_cfg_t3[QLR_CFG_TYPE] = 2;

      // Reset values (TODO: reset via mul)
      curr_C[0] = 0;
      curr_C[1] = 0;
      curr_C[2] = 0;
      curr_C[3] = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
        qlr_t0 = matrix_A[y * num_cols_A + i];
        qlr_t1 = matrix_A[(y + 1) * num_cols_A + i];
        qlr_t2 = matrix_B[i * num_cols_B + x];
        qlr_t3 = matrix_B[i * num_cols_B + x + 1];
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
        qlr_t0 = matrix_A[y * num_cols_A + i + 1];
        qlr_t1 = matrix_A[(y + 1) * num_cols_A + i + 1];
        qlr_t2 = matrix_B[(i + 1) * num_cols_B + x];
        qlr_t3 = matrix_B[(i + 1) * num_cols_B + x + 1];
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
      }

      // Store values
      anchor_row_0 = y * num_cols_C + x;
      anchor_row_1 = anchor_row_0 + num_cols_C;
      matrix_C[anchor_row_0] = curr_C[0];
      matrix_C[anchor_row_0 + 1] = curr_C[1];
      matrix_C[anchor_row_1] = curr_C[2];
      matrix_C[anchor_row_1 + 1] = curr_C[3];
    }
  }
}

// column producing processing element
void systolic_cp_pe(const uint32_t col_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ B,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *matrix_B;
  int32_t *matrix_C;
  uint32_t num_cols_B;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  register int32_t curr_C[4];
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Get matrix arrays
  matrix_B = B->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_B = B->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Configure QLRs
  if (col_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_RF] = 2;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[0][col_idx];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_RF] = 2;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[0][col_idx];
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][col_idx];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_1[1][col_idx];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_RF] = 2;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[0][col_idx];
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_RF] = 2;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[0][col_idx];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][col_idx];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_1[1][col_idx];
  }

  // Check if PE is at the right boundary
  if (col_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x
        shifted_x = x + 2 * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C) {
          write_csr(0, shifted_x);
          write_csr(1, y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          qlr_cfg_t2[QLR_CFG_TYPE] = 2;
          qlr_cfg_t3[QLR_CFG_TYPE] = 2;

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            qlr_t2 = matrix_B[i * num_cols_B + shifted_x];
            qlr_t3 = matrix_B[i * num_cols_B + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            qlr_t2 = matrix_B[(i + 1) * num_cols_B + shifted_x];
            qlr_t3 = matrix_B[(i + 1) * num_cols_B + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
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
          write_csr(0, shifted_x);
          write_csr(1, y);
          // Start QLRs (do not push past boundary of matrix C)
          if (shifted_x == num_cols_C - 2) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
          }
          qlr_cfg_t2[QLR_CFG_TYPE] = 2;
          qlr_cfg_t3[QLR_CFG_TYPE] = 2;

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            qlr_t2 = matrix_B[i * num_cols_B + shifted_x];
            qlr_t3 = matrix_B[i * num_cols_B + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            qlr_t2 = matrix_B[(i + 1) * num_cols_B + shifted_x];
            qlr_t3 = matrix_B[(i + 1) * num_cols_B + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }
}

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx, const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ A,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *matrix_A;
  int32_t *matrix_C;
  uint32_t num_cols_A;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_y;
  register int32_t curr_C[4];
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Get matrix arrays
  matrix_A = A->matrix;
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_cols_A = A->num_cols;
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Configure QLRs
  if (row_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_RF] = 2;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_RF] = 2;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_1[row_idx][0];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_RF] = 2;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][0];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_RF] = 2;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_1[row_idx][0];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_1[row_idx + 1][0];
  }

  // Check if PE is at the bottom boundary
  if (row_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < num_rows_C) {
          write_csr(0, x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 2;
          qlr_cfg_t1[QLR_CFG_TYPE] = 2;
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            qlr_t0 = matrix_A[shifted_y * num_cols_A + i];
            qlr_t1 = matrix_A[(shifted_y + 1) * num_cols_A + i];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            qlr_t0 = matrix_A[shifted_y * num_cols_A + i + 1];
            qlr_t1 = matrix_A[(shifted_y + 1) * num_cols_A + i + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
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
          write_csr(0, x);
          write_csr(1, shifted_y);
          // Start QLRs (do not push past boundary of matrix C)
          qlr_cfg_t0[QLR_CFG_TYPE] = 2;
          qlr_cfg_t1[QLR_CFG_TYPE] = 2;
          if (shifted_y == num_rows_C - 2) {
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < 2 * rep_count; i += 2) {
            qlr_t0 = matrix_A[shifted_y * num_cols_A + i];
            qlr_t1 = matrix_A[(shifted_y + 1) * num_cols_A + i];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            qlr_t0 = matrix_A[shifted_y * num_cols_A + i + 1];
            qlr_t1 = matrix_A[(shifted_y + 1) * num_cols_A + i + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }
}

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t rep_count,
                    systolic_matrix_t const *__restrict__ C) {
  int32_t *matrix_C;
  uint32_t num_rows_C;
  uint32_t num_cols_C;
  uint32_t shifted_x;
  uint32_t shifted_y;
  register int32_t curr_C[4];
  uint32_t anchor_row_0;
  uint32_t anchor_row_1;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Get matrix arrays
  matrix_C = C->matrix;

  // Get dimensions of matrices
  num_rows_C = C->num_rows;
  num_cols_C = C->num_cols;

  // Configure QLRs
  if (col_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_RF] = 2;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_RF] = 2;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t0[QLR_CFG_RF] = 2;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t1[QLR_CFG_RF] = 2;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][col_idx + 1];
  }
  if (row_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_RF] = 2;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][col_idx];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_RF] = 2;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_1[row_idx][col_idx];
  } else {
    qlr_cfg_t2[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t2[QLR_CFG_RF] = 2;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][col_idx];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][col_idx];
    qlr_cfg_t3[QLR_CFG_REQ] = 2 * rep_count;
    qlr_cfg_t3[QLR_CFG_RF] = 2;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_1[row_idx][col_idx];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_1[row_idx + 1][col_idx];
  }

  // PE is not at a boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs (TODO: POTENTIAL DEADLOCK DUE TO SLOW ENABLE)
          if (shifted_x == num_cols_C - 2) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
          }
          if (shifted_y == num_rows_C - 2) {
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }

  // PE is at the right boundary
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          if (shifted_y == num_rows_C - 2) {
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }

  // PE is at the bottom boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          if (shifted_x == num_cols_C - 2) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
          }
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }

  // PE is at the bottom right corner
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < num_rows_C; y += 2 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < num_cols_C; x += 2 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 2 * col_idx;
        shifted_y = y + 2 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < num_cols_C && shifted_y < num_rows_C) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          curr_C[0] = 0;
          curr_C[1] = 0;
          curr_C[2] = 0;
          curr_C[3] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < rep_count; ++i) {
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[0]) : "r"(qlr_t0), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[1]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[2]) : "r"(qlr_t1), "r"(qlr_t2));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(curr_C[3]) : "r"(qlr_t1), "r"(qlr_t3));
          }

          // Store values
          anchor_row_0 = shifted_y * num_cols_C + shifted_x;
          anchor_row_1 = anchor_row_0 + num_cols_C;
          matrix_C[anchor_row_0] = curr_C[0];
          matrix_C[anchor_row_0 + 1] = curr_C[1];
          matrix_C[anchor_row_1] = curr_C[2];
          matrix_C[anchor_row_1 + 1] = curr_C[3];
        }
      }
    }
  }
}
