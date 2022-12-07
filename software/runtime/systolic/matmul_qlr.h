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
 *
 * Matrix is processed in 3x3 submatrices with the following indexing
 *
 *      B B B          B0 B1 B2
 *
 *   A  C C C      A0  C0 C1 C2
 *   A  C C C  =>  A1  C3 C4 C5
 *   A  C C C      A2  C6 C7 C8
 *
 * e.g. C0 = A0 * B0  or  C7 = A2 * B1
 *
 * We use three QLRs for A and one QLR for B, providing the vector of A
 * at once and then iterating over the vector of B, provided one element
 * at a time. This unbalanced submatrix multiplication requires 12 queue
 * operations per 9 MACs
 *
 *    B2 B1 B0 > t3
 *
 *   A0 > t0  C0 C1 C2
 *   A1 > t1  C3 C4 C5
 *   A2 > t2  C6 C7 C8
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"

// Dimensions of square systolic array
#define SYSTOLIC_SIZE 16

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

// TODO: SQRT ROOT OF NUM_CORES FOR SYSTOLIC SIZE

// Array of queue ptrs in row-major order
int32_t *queues_horz_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_1[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_horz_2[SYSTOLIC_SIZE][SYSTOLIC_SIZE];
int32_t *queues_vert_0[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t grid_pos = 0;
  uint32_t core_id;
  uint32_t offset;
  for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
    for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
      core_id = core_map[grid_pos];
      offset = core_id * sizeof(int32_t);
      queues_horz_0[y][x] = (int32_t *)(offset + 0);
      queues_horz_1[y][x] = (int32_t *)(offset + 1);
      queues_horz_2[y][x] = (int32_t *)(offset + 2);
      queues_vert_0[y][x] = (int32_t *)(offset + 3);
      ++grid_pos;
    }
  }

  // Print out queue addresses
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
  // printf("queues_horz_2\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_horz_2[y][x]);
  //   }
  //   printf("\n");
  // }
  // printf("queues_vert_0\n");
  // for (uint32_t y = 0; y < SYSTOLIC_SIZE; ++y) {
  //   for (uint32_t x = 0; x < SYSTOLIC_SIZE; ++x) {
  //     printf("%5d ", queues_vert_0[y][x]);
  //   }
  //   printf("\n");
  // }
}

// row and column producing processing element
void systolic_rcp_pe(const uint32_t num_cores, const uint32_t M,
                     const uint32_t N, const uint32_t P,
                     int32_t const *__restrict__ A,
                     int32_t const *__restrict__ B,
                     int32_t *__restrict__ C) {
  register int32_t sub_C[9];
  register int32_t qlr_t3_buffer;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Configure QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][1];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][1];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[0][1];
  qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
  qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][0];

  // Synchronize cores
  mempool_sleep_barrier(num_cores);

  // Execute step-wise matrix multiplication
  for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
    for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
      write_csr(0, x);
      write_csr(1, y);
      // Start QLRs
      qlr_cfg_t0[QLR_CFG_TYPE] = 2;
      qlr_cfg_t1[QLR_CFG_TYPE] = 2;
      qlr_cfg_t2[QLR_CFG_TYPE] = 2;
      qlr_cfg_t3[QLR_CFG_TYPE] = 2;

      // Reset values (TODO: reset via mul)
      sub_C[0] = 0;
      sub_C[1] = 0;
      sub_C[2] = 0;
      sub_C[3] = 0;
      sub_C[4] = 0;
      sub_C[5] = 0;
      sub_C[6] = 0;
      sub_C[7] = 0;
      sub_C[8] = 0;

      // Systolic matrix multiplication through MACs
      for (uint32_t i = 0; i < N; ++i) {
        qlr_t3 = B[i * P + x + 0];
        qlr_t0 = A[(y + 0) * N + i];
        qlr_t1 = A[(y + 1) * N + i];
        qlr_t2 = A[(y + 2) * N + i];
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3_buffer = B[i * P + x + 1];
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3 = qlr_t3_buffer;
        qlr_t3_buffer = B[i * P + x + 2];
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
        __asm__ __volatile__("" : "=m"(*(int32_t *)B));
        qlr_t3 = qlr_t3_buffer;
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
        __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
      }

      // Store values
      C[(y + 0) * P + (x + 0)] = sub_C[0];
      C[(y + 1) * P + (x + 0)] = sub_C[1];
      C[(y + 2) * P + (x + 0)] = sub_C[2];
      C[(y + 0) * P + (x + 1)] = sub_C[3];
      C[(y + 1) * P + (x + 1)] = sub_C[4];
      C[(y + 2) * P + (x + 1)] = sub_C[5];
      C[(y + 0) * P + (x + 2)] = sub_C[6];
      C[(y + 1) * P + (x + 2)] = sub_C[7];
      C[(y + 2) * P + (x + 2)] = sub_C[8];
    }
  }
}

// column producing processing element
void systolic_cp_pe(const uint32_t num_cores, const uint32_t col_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ B, int32_t *__restrict__ C) {
  uint32_t shifted_x;
  register int32_t sub_C[9];
  register int32_t qlr_t3_buffer;
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Configure QLRs
  if (col_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_RF] = 3;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[0][col_idx];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_RF] = 3;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[0][col_idx];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_RF] = 3;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[0][col_idx];
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][col_idx];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_RF] = 3;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[0][col_idx];
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[0][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_RF] = 3;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[0][col_idx];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[0][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_RF] = 3;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[0][col_idx];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[0][col_idx + 1];
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[1][col_idx];
  }

  // Synchronize cores
  mempool_sleep_barrier(num_cores);

  // Check if PE is at the right boundary
  if (col_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x
        shifted_x = x + 3 * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P) {
          write_csr(0, shifted_x);
          write_csr(1, y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          qlr_cfg_t3[QLR_CFG_TYPE] = 2;

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            qlr_t3 = B[i * P + shifted_x + 0];
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3_buffer = B[i * P + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3 = qlr_t3_buffer;
            qlr_t3_buffer = B[i * P + shifted_x + 2];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3 = qlr_t3_buffer;
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x
        shifted_x = x + 3 * col_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P) {
          write_csr(0, shifted_x);
          write_csr(1, y);
          // Start QLRs (do not push past boundary of matrix C)
          if (shifted_x == P - 3) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
          }
          qlr_cfg_t3[QLR_CFG_TYPE] = 2;

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            qlr_t3 = B[i * P + shifted_x + 0];
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3_buffer = B[i * P + shifted_x + 1];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3 = qlr_t3_buffer;
            qlr_t3_buffer = B[i * P + shifted_x + 2];
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=m"(*(int32_t *)B));
            qlr_t3 = qlr_t3_buffer;
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  }
}

// row producing processing element
void systolic_rp_pe(const uint32_t num_cores, const uint32_t row_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ A, int32_t *__restrict__ C) {
  uint32_t shifted_y;
  register int32_t sub_C[9];
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Configure QLRs
  if (row_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][1];
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_RF] = 3;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][1];
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_RF] = 3;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][0];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][0];
  }

  // Synchronize cores
  mempool_sleep_barrier(num_cores);

  // Check if PE is at the bottom boundary
  if (row_idx == SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < M) {
          write_csr(0, x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 2;
          qlr_cfg_t1[QLR_CFG_TYPE] = 2;
          qlr_cfg_t2[QLR_CFG_TYPE] = 2;
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            qlr_t0 = A[(shifted_y + 0) * N + i];
            qlr_t1 = A[(shifted_y + 1) * N + i];
            qlr_t2 = A[(shifted_y + 2) * N + i];
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (x + 2)] = sub_C[8];
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift y
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_y < M) {
          write_csr(0, x);
          write_csr(1, shifted_y);
          // Start QLRs (do not push past boundary of matrix C)
          qlr_cfg_t0[QLR_CFG_TYPE] = 2;
          qlr_cfg_t1[QLR_CFG_TYPE] = 2;
          qlr_cfg_t2[QLR_CFG_TYPE] = 2;
          if (shifted_y == M - 3) {
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            qlr_t0 = A[(shifted_y + 0) * N + i];
            qlr_t1 = A[(shifted_y + 1) * N + i];
            qlr_t2 = A[(shifted_y + 2) * N + i];
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (x + 2)] = sub_C[8];
        }
      }
    }
  }
}

// non-producing processing element
void systolic_np_pe(const uint32_t num_cores, const uint32_t row_idx,
                    const uint32_t col_idx, const uint32_t M, const uint32_t N,
                    const uint32_t P, int32_t *__restrict__ C) {
  uint32_t shifted_x;
  uint32_t shifted_y;
  register int32_t sub_C[9];
  volatile uint32_t *qlr_cfg_t0 = (uint32_t *)QLR_CFG_T0;
  volatile uint32_t *qlr_cfg_t1 = (uint32_t *)QLR_CFG_T1;
  volatile uint32_t *qlr_cfg_t2 = (uint32_t *)QLR_CFG_T2;
  volatile uint32_t *qlr_cfg_t3 = (uint32_t *)QLR_CFG_T3;

  // Configure QLRs
  if (col_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_RF] = 3;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_RF] = 3;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_RF] = 3;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[row_idx][col_idx];
  } else {
    qlr_cfg_t0[QLR_CFG_REQ] = N;
    qlr_cfg_t0[QLR_CFG_RF] = 3;
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_REQ] = N;
    qlr_cfg_t1[QLR_CFG_RF] = 3;
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_REQ] = N;
    qlr_cfg_t2[QLR_CFG_RF] = 3;
    qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[row_idx][col_idx];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][col_idx + 1];
  }
  if (row_idx == SYSTOLIC_SIZE - 1) {
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_RF] = 3;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][col_idx];
  } else {
    qlr_cfg_t3[QLR_CFG_REQ] = 3 * N;
    qlr_cfg_t3[QLR_CFG_RF] = 3;
    qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_vert_0[row_idx][col_idx];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_vert_0[row_idx + 1][col_idx];
  }

  // Synchronize cores
  mempool_sleep_barrier(num_cores);

  // PE is not at a boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 3 * col_idx;
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          if (shifted_x == P - 3) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
          }
          if (shifted_y == M - 3) {
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  }

  // PE is at the right boundary
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx != SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 3 * col_idx;
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          if (shifted_y == M - 3) {
            qlr_cfg_t3[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t3[QLR_CFG_TYPE] = 3;
          }

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  }

  // PE is at the bottom boundary
  if ((col_idx != SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 3 * col_idx;
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          if (shifted_x == P - 3) {
            qlr_cfg_t0[QLR_CFG_TYPE] = 1;
            qlr_cfg_t1[QLR_CFG_TYPE] = 1;
            qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          } else {
            qlr_cfg_t0[QLR_CFG_TYPE] = 3;
            qlr_cfg_t1[QLR_CFG_TYPE] = 3;
            qlr_cfg_t2[QLR_CFG_TYPE] = 3;
          }
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  }

  // PE is at the bottom right corner
  if ((col_idx == SYSTOLIC_SIZE - 1) && (row_idx == SYSTOLIC_SIZE - 1)) {
    // Execute step-wise matrix multiplication
    for (uint32_t y = 0; y < M; y += 3 * SYSTOLIC_SIZE) {
      for (uint32_t x = 0; x < P; x += 3 * SYSTOLIC_SIZE) {
        // Shift x and y
        shifted_x = x + 3 * col_idx;
        shifted_y = y + 3 * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          write_csr(0, shifted_x);
          write_csr(1, shifted_y);
          // Start QLRs
          qlr_cfg_t0[QLR_CFG_TYPE] = 1;
          qlr_cfg_t1[QLR_CFG_TYPE] = 1;
          qlr_cfg_t2[QLR_CFG_TYPE] = 1;
          qlr_cfg_t3[QLR_CFG_TYPE] = 1;

          // Reset values (TODO: reset via mul)
          sub_C[0] = 0;
          sub_C[1] = 0;
          sub_C[2] = 0;
          sub_C[3] = 0;
          sub_C[4] = 0;
          sub_C[5] = 0;
          sub_C[6] = 0;
          sub_C[7] = 0;
          sub_C[8] = 0;

          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N; ++i) {
            __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[0]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[1]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[2]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[3]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[4]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[5]) : "r"(qlr_t2), "r"(qlr_t3));
            __asm__ __volatile__("" : "=r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[6]) : "r"(qlr_t0), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[7]) : "r"(qlr_t1), "r"(qlr_t3));
            __asm__ __volatile__("p.mac %0, %1, %2" : "+r"(sub_C[8]) : "r"(qlr_t2), "r"(qlr_t3));
          }

          // Store values
          C[(shifted_y + 0) * P + (shifted_x + 0)] = sub_C[0];
          C[(shifted_y + 1) * P + (shifted_x + 0)] = sub_C[1];
          C[(shifted_y + 2) * P + (shifted_x + 0)] = sub_C[2];
          C[(shifted_y + 0) * P + (shifted_x + 1)] = sub_C[3];
          C[(shifted_y + 1) * P + (shifted_x + 1)] = sub_C[4];
          C[(shifted_y + 2) * P + (shifted_x + 1)] = sub_C[5];
          C[(shifted_y + 0) * P + (shifted_x + 2)] = sub_C[6];
          C[(shifted_y + 1) * P + (shifted_x + 2)] = sub_C[7];
          C[(shifted_y + 2) * P + (shifted_x + 2)] = sub_C[8];
        }
      }
    }
  }
}
