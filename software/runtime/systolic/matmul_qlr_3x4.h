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
//         Sergio Mazzola, ETH Zurich

/*
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 *
 * Each PE processes C in 3x3 submatrices with the following indexing
 *
 *      B B B          B0 B1 B2 B3
 *
 *   A  C C C      A0  C0 C3 C6 C9
 *   A  C C C  =>  A1  C1 C4 C7 C10
 *   A  C C C      A2  C2 C5 C8 C11
 *
 * e.g. C0 = A0 * B0  or  C7 = A2 * B1
 *
 * We use three QLRs for A and one QLR for B, providing [A0, A1, A2] all
 * at once and iterating over the vector [B0, B1, B2], providing one element
 * at a time. This unbalanced submatrix multiplication requires 12 queue
 * operations (6 pops + 6 pushes) per 9 MACs
 *
 *    B3 B2 B1 B0 > t3
 *
 *   A0 > t0   C0 C3 C6 C9
 *   A1 > t1   C1 C4 C7 C10
 *   A2 > t2   C2 C5 C8 C11
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "qlr.h"

// Settings
#define UNROLL_X 4 // hardcoded, do not change
#define UNROLL_Y 3 // hardcoded, do not change
#define PRINTF_OUT_CHUNK 0

// Systolic grid
#if NUM_CORES == 16
// 16 cores -> 4x4 systolic array
#define SYSTOLIC_SIZE 4
#elif NUM_CORES == 256
// 256 cores -> 16x16 systolic array
#define SYSTOLIC_SIZE 16
#else
// unsupported number of cores
#error Unsupported NUM_CORES
#endif

// Array of queue pointers in row-major order
int32_t *queues_horz_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_1[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_2[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_vert_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t core_id;
  uint32_t offset;
  for (uint32_t row = 0; row < SYSTOLIC_SIZE; row++) {
    for (uint32_t col = 0; col < SYSTOLIC_SIZE; col++) {
      core_id = core_map[row * SYSTOLIC_SIZE + col];
      offset = core_id * NUM_QUEUES_PER_CORE;
      queues_horz_0[row][col] = (int32_t *)(offset + 0);
      queues_horz_1[row][col] = (int32_t *)(offset + 1);
      queues_horz_2[row][col] = (int32_t *)(offset + 2);
      queues_vert_0[row][col] = (int32_t *)(offset + 3);
    }
  }
}

// print starting point of parallelized 3x3 output chunk
#define PRINT_CHUNK_XY(X, Y) \
  do {                       \
    write_csr(0, (X));       \
    write_csr(1, (Y));       \
  } while(0)

#define DEFINE_QLR_CONFIG                                 \
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0; \
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1; \
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2; \
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3

#define MAC_SUBCOL_3X1(ROW_0, ROW_1, ROW_2)                                                     \
  do {                                                                                          \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[(ROW_0)]) : "r"(qlr_t0), "r"(qlr_t3)); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[(ROW_1)]) : "r"(qlr_t1), "r"(qlr_t3)); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[(ROW_2)]) : "r"(qlr_t2), "r"(qlr_t3)); \
  } while(0)

#define RESET_SUB_C \
  do {              \
    sub_C[0]  = 0;  \
    sub_C[1]  = 0;  \
    sub_C[2]  = 0;  \
    sub_C[3]  = 0;  \
    sub_C[4]  = 0;  \
    sub_C[5]  = 0;  \
    sub_C[6]  = 0;  \
    sub_C[7]  = 0;  \
    sub_C[8]  = 0;  \
    sub_C[9]  = 0;  \
    sub_C[10] = 0;  \
    sub_C[11] = 0;  \
  } while(0)

#define STORE_SUB_C(BASE_Y, BASE_X)                     \
  do {                                                  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 0)] = sub_C[0];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 0)] = sub_C[1];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 0)] = sub_C[2];  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 1)] = sub_C[3];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 1)] = sub_C[4];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 1)] = sub_C[5];  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 2)] = sub_C[6];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 2)] = sub_C[7];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 2)] = sub_C[8];  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 3)] = sub_C[9];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 3)] = sub_C[10]; \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 3)] = sub_C[11]; \
  } while(0)


// row- and column-producing processing element
void systolic_rcp_pe(const uint32_t M, const uint32_t N,
                     const uint32_t P,
                     int32_t const *__restrict__ A,
                     int32_t const *__restrict__ B,
                     int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];
  // same for QLR buffer for B elements
  register int32_t qlr_t3_buffer;

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // Configure QLRs
  // outputs (horizontal)
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][1];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][1];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[0][1];
  // outputs (vertical)
  qlr_cfg_t3[QLR_CFG_REQ] = UNROLL_X * N;
  qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][0];

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
      #if PRINTF_OUT_CHUNK
      PRINT_CHUNK_XY(x, y);
      #endif
      // Start QLRs
      qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
      qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
      qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
      qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_OQLR;

      // Reset submatrix accumulator
      RESET_SUB_C;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < N; ++i) {
        // load through normal load instructions
        qlr_t3 = B[i * P + x + 0];
        qlr_t0 = A[(y + 0) * N + i];
        qlr_t1 = A[(y + 1) * N + i];
        qlr_t2 = A[(y + 2) * N + i];
        // prevent reordering of memory operations
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3_buffer = B[i * P + x + 1];
        MAC_SUBCOL_3X1(0, 1, 2);
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3 = qlr_t3_buffer;
        qlr_t3_buffer = B[i * P + x + 2];
        MAC_SUBCOL_3X1(3, 4, 5);
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3 = qlr_t3_buffer;
        qlr_t3_buffer = B[i * P + x + 3];
        MAC_SUBCOL_3X1(6, 7, 8);
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3 = qlr_t3_buffer;
        MAC_SUBCOL_3X1(9, 10, 11);
      }

      // Store values
      STORE_SUB_C(y, x);
    }
  }
}


#define COMPUTATION_CP_PE                                                \
  do {                                                                   \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2)); \
    qlr_t3 = B[i * P + shifted_x + 0];                                   \
    __asm__ __volatile__("" : "=m"(*(int32_t *)B));                      \
    qlr_t3_buffer = B[i * P + shifted_x + 1];                            \
    MAC_SUBCOL_3X1(0, 1, 2);                                             \
    __asm__ __volatile__("" : "=m"(*(int32_t *)B));                      \
    qlr_t3 = qlr_t3_buffer;                                              \
    qlr_t3_buffer = B[i * P + shifted_x + 2];                            \
    MAC_SUBCOL_3X1(3, 4, 5);                                             \
    __asm__ __volatile__("" : "=m"(*(int32_t *)B));                      \
    qlr_t3 = qlr_t3_buffer;                                              \
    qlr_t3_buffer = B[i * P + shifted_x + 3];                            \
    MAC_SUBCOL_3X1(6, 7, 8);                                             \
    __asm__ __volatile__("" : "=m"(*(int32_t *)B));                      \
    qlr_t3 = qlr_t3_buffer;                                              \
    MAC_SUBCOL_3X1(9, 10, 11);                                           \
  } while (0)

// column-producing processing element
void systolic_cp_pe(const uint32_t col_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ B, int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];
  // same for QLR buffer for B elements
  register int32_t qlr_t3_buffer;

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // actual C coordinates
  uint32_t shifted_x;

  // Configure QLRs

  // inputs (horizontal)
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[0][col_idx];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[0][col_idx];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[0][col_idx];
  // outputs (horizontal)
  if (col_idx != SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[0][col_idx + 1];
  }
  // outputs (vertical)
  qlr_cfg_t3[QLR_CFG_REQ] = UNROLL_X * N;
  qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][col_idx];

  // Check if PE is at the right boundary
  if (col_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x (y is constant)
        // i.e., move to the correct C matrix output chunk (for parallelization)
        shifted_x = x + UNROLL_X * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, y);
          #endif
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_OQLR;

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_CP_PE;
          }

          // Store values
          STORE_SUB_C(y, shifted_x);
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x (y is constant)
        // i.e., move to the correct C matrix output chunk (for parallelization)
        shifted_x = x + UNROLL_X * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, y);
          #endif
          // Start QLRs (do not push past boundary of matrix C)
          // i.e., we are within SYSTOLIC_SIZE (not on boundary) but at the end of C
          if (shifted_x == P - UNROLL_X) {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }
          qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_OQLR;

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_CP_PE;
          }

          // Store values
          STORE_SUB_C(y, shifted_x);
        }
      }
    }
  }
}


#define COMPUTATION_RP_PE                                                \
  do {                                                                   \
    qlr_t0 = A[(shifted_y + 0) * N + i];                                 \
    qlr_t1 = A[(shifted_y + 1) * N + i];                                 \
    qlr_t2 = A[(shifted_y + 2) * N + i];                                 \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(0, 1, 2);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(3, 4, 5);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(6, 7, 8);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(9, 10, 11);                                           \
  } while (0)

// row producing processing element
void systolic_rp_pe(const uint32_t row_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ A, int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // actual C coordinates
  uint32_t shifted_y;

  // Configure QLRs
  if (row_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][1];
    qlr_cfg_t3[QLR_CFG_REQ] = UNROLL_X * N;
    qlr_cfg_t3[QLR_CFG_RF] = UNROLL_Y;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][1];
    qlr_cfg_t3[QLR_CFG_REQ] = UNROLL_X * N;
    qlr_cfg_t3[QLR_CFG_RF] = UNROLL_Y;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][0];
  }

  // Check if PE is at the bottom boundary
  if (row_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift y (x is constant)
        // i.e., move to the correct C matrix output chunk (for parallelization)
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(x, shifted_y);
          #endif
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_RP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, x);
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(x, shifted_y);
          #endif
          // Start QLRs (do not push past boundary of matrix C)
          qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
          if (shifted_y == M - UNROLL_Y) {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_RP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, x);
        }
      }
    }
  }
}


#define COMPUTATION_NP_PE                                                \
  do {                                                                   \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2)); \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(0, 1, 2);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(3, 4, 5);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(6, 7, 8);                                             \
    __asm__ __volatile__("" : "=r"(qlr_t3));                             \
    MAC_SUBCOL_3X1(9, 10, 11);                                           \
  } while (0)

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // actual C coordinates
  uint32_t shifted_x;
  uint32_t shifted_y;

  // Configure QLRs

  // inputs (horizontal)
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[row_idx][col_idx];
  // inputs (vertical)
  qlr_cfg_t3[QLR_CFG_REQ] = UNROLL_X * N;
  qlr_cfg_t3[QLR_CFG_RF] = UNROLL_Y;
  qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][col_idx];
  // outputs (horizontal)
  if (col_idx != SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][col_idx + 1];
  }
  if (row_idx != SYSTOLIC_SIZE - 1) {
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][col_idx];
  }

  // PE is not at a boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + UNROLL_X * col_idx;
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, shifted_y);
          #endif
          // Start QLRs
          if (shifted_x == P - UNROLL_X) {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }
          if (shifted_y == M - UNROLL_Y) {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_NP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  }

  // PE is at the right boundary
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + UNROLL_X * col_idx;
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, shifted_y);
          #endif
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          if (shifted_y == M - 3) {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_NP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  }

  // PE is at the bottom boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + UNROLL_X * col_idx;
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, shifted_y);
          #endif
          // Start QLRs
          if (shifted_x == P - UNROLL_X) {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
          }
          qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_NP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  }

  // PE is at the bottom right corner
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + UNROLL_X * col_idx;
        shifted_y = y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, shifted_y);
          #endif
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

          // Reset submatrix accumulator
          RESET_SUB_C;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            COMPUTATION_NP_PE;
          }

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  }
}
