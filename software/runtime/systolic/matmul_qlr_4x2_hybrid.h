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
 * Each PE processes C in 4x2 submatrices.
 * We use all four QLRs for A; B is loaded from memory by each individual PE.
 *
 *             B0 B1 < loaded from L1
 *
 *   A0 > t0   C0 C3
 *   A1 > t1   C1 C4
 *   A2 > t2   C2 C5
 *   A3 > t3   C3 C6
 *      (QLRs)
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "qlr.h"

// Settings
#define UNROLL_X 2 // hardcoded, do not change
#define UNROLL_Y 4 // hardcoded, do not change
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
int32_t *queues_horz_3[SYSTOLIC_SIZE][SYSTOLIC_SIZE];

void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t core_id;
  uint32_t offset;
  for (uint32_t row = 0; row < SYSTOLIC_SIZE; row++) {
    for (uint32_t col = 0; col < SYSTOLIC_SIZE; col++) {
      core_id = core_map[row * SYSTOLIC_SIZE + col];
      // Every core is assigned its own 4 queues (banking factor
      // should be 4), which are local to the core's tile. The
      // queues are then placed in a 2D array in the same scheme
      // of 'core_map'. Neighbouring cores are later connected
      // through the QLRs configuration to form the systolic array.
      offset = core_id * NUM_QUEUES_PER_CORE;
      queues_horz_0[row][col] = (int32_t *)(offset + 0);
      queues_horz_1[row][col] = (int32_t *)(offset + 1);
      queues_horz_2[row][col] = (int32_t *)(offset + 2);
      queues_horz_3[row][col] = (int32_t *)(offset + 3);
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

#define MAC_SUBCOL_3X1(C_0, C_1, C_2, C_3, B)                                       \
  do {                                                                              \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_0)) : "r"(qlr_t0), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_1)) : "r"(qlr_t1), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_2)) : "r"(qlr_t2), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_3)) : "r"(qlr_t3), "r"((B))); \
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
  } while(0)

#define STORE_SUB_C(BASE_Y, BASE_X)                     \
  do {                                                  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 0)] = sub_C[0];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 0)] = sub_C[1];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 0)] = sub_C[2];  \
    C[((BASE_Y) + 3) * P + ((BASE_X) + 0)] = sub_C[3];  \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 1)] = sub_C[4];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 1)] = sub_C[5];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 1)] = sub_C[6];  \
    C[((BASE_Y) + 3) * P + ((BASE_X) + 1)] = sub_C[7];  \
  } while(0)


// row producing processing element
void systolic_rp_pe(const uint32_t row_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ A, int32_t const *__restrict__ B,
                    int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];
  register int32_t sub_row_B[UNROLL_X];

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // actual C coordinates
  uint32_t shifted_y;

  // Configure QLRs (only output QLRs)
  // load a 4-element sub-col of A and push through OQLRs
  // for B, load directly from memory without using QLRs
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][1];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][1];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][1];
  qlr_cfg_t3[QLR_CFG_REQ] = N;
  qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_horz_3[row_idx][1];

  // Execute step-wise matrix multiplication
  for (uint32_t base_y = 0; base_y < M; base_y += UNROLL_Y * SYSTOLIC_SIZE) {
    for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * SYSTOLIC_SIZE) {
      // Shift base_y (base_x is constant)
      // i.e., move to the correct C matrix output chunk (for parallelization)
      shifted_y = base_y + UNROLL_Y * row_idx;

      // Check if this PE is currently within the matrix C
      if (shifted_y < M) {
        #if PRINTF_OUT_CHUNK
        PRINT_CHUNK_XY(base_x, shifted_y);
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
          sub_row_B[0] = B[i * P + base_x + 0];
          qlr_t0 = A[(shifted_y + 0) * N + i];
          qlr_t1 = A[(shifted_y + 1) * N + i];
          qlr_t2 = A[(shifted_y + 2) * N + i];
          qlr_t3 = A[(shifted_y + 3) * N + i];
          sub_row_B[1] = B[i * P + base_x + 1];
          __asm__ __volatile__("" : "=m"(*(int32_t *)B));
          // column 1
          MAC_SUBCOL_3X1(sub_C[0], sub_C[1], sub_C[2], sub_C[3], sub_row_B[0]);
          // column 2
          MAC_SUBCOL_3X1(sub_C[4], sub_C[5], sub_C[6], sub_C[7], sub_row_B[1]);
        }

        // Store values
        STORE_SUB_C(shifted_y, base_x);
      }
    }
  }
}


#define COMPUTATION_NP_PE                                                              \
  do {                                                                                 \
    sub_row_B[0] = B[i * P + shifted_x + 0];                                                   \
    sub_row_B[1] = B[i * P + shifted_x + 1];                                                   \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2), "=r"(qlr_t3)); \
    MAC_SUBCOL_3X1(sub_C[0], sub_C[1], sub_C[2], sub_C[3], sub_row_B[0]);              \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1), "=r"(qlr_t2), "=r"(qlr_t3)); \
    MAC_SUBCOL_3X1(sub_C[4], sub_C[5], sub_C[6], sub_C[7], sub_row_B[1]);              \
  } while (0)

// non-producing processing element
void systolic_np_pe(const uint32_t row_idx, const uint32_t col_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ B, int32_t *__restrict__ C) {
  // always keep output in regfile
  register int32_t sub_C[UNROLL_X * UNROLL_Y];
  register int32_t sub_row_B[UNROLL_X];

  // pointers to QLR config
  DEFINE_QLR_CONFIG;

  // actual C coordinates
  uint32_t shifted_x;
  uint32_t shifted_y;

  // Configure QLRs

  // horizontal inputs (from col 1 to SYSTOLIC_SIZE-1)
  qlr_cfg_t0[QLR_CFG_REQ] = N;
  qlr_cfg_t0[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_horz_0[row_idx][col_idx];
  qlr_cfg_t1[QLR_CFG_REQ] = N;
  qlr_cfg_t1[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_horz_1[row_idx][col_idx];
  qlr_cfg_t2[QLR_CFG_REQ] = N;
  qlr_cfg_t2[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t2[QLR_CFG_IADDR] = (uint32_t)queues_horz_2[row_idx][col_idx];
  qlr_cfg_t3[QLR_CFG_REQ] = N;
  qlr_cfg_t3[QLR_CFG_RF] = UNROLL_X;
  qlr_cfg_t3[QLR_CFG_IADDR] = (uint32_t)queues_horz_3[row_idx][col_idx];
  // horizontal outputs (from col 1 to SYSTOLIC_SIZE-2)
  if (col_idx != SYSTOLIC_SIZE - 1) {
    qlr_cfg_t0[QLR_CFG_OADDR] = (uint32_t)queues_horz_0[row_idx][col_idx + 1];
    qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_horz_1[row_idx][col_idx + 1];
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_horz_2[row_idx][col_idx + 1];
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_horz_3[row_idx][col_idx + 1];
  }

  if (col_idx != SYSTOLIC_SIZE - 1) {
    // Execute step-wise matrix multiplication
    for (uint32_t base_y = 0; base_y < M; base_y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift base_x and base_y
        shifted_x = base_x + UNROLL_X * col_idx;
        shifted_y = base_y + UNROLL_Y * row_idx;

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
            qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
          } else {
            // only activate output QLRs if we are not in the last matrix column
            qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
            qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_IOQLR;
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
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t base_y = 0; base_y < M; base_y += UNROLL_Y * SYSTOLIC_SIZE) {
      for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * SYSTOLIC_SIZE) {
        // Shift base_x and base_y
        shifted_x = base_x + UNROLL_X * col_idx;
        shifted_y = base_y + UNROLL_Y * row_idx;

        // Check if this PE is currently within the matrix C
        if (shifted_x < P && shifted_y < M) {
          #if PRINTF_OUT_CHUNK
          PRINT_CHUNK_XY(shifted_x, shifted_y);
          #endif
          // Start QLRs
          // we are in the last PE column, no output QLRs
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
