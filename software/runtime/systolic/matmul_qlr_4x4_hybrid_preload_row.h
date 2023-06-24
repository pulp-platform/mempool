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
 * Each PE processes C in 4x4 submatrices.
 * We use all four QLRs for A's rows; B is loaded from memory by each individual PE.
 *
 *             B3 B2 B1 B0 < loaded from L1
 *
 *   A0 > t0   C0 C4 C8  C12
 *   A1 > t1   C1 C5 C9  C13
 *   A2 > t2   C2 C6 C10 C14
 *   A3 > t3   C3 C7 C11 C15
 *      (QLRs)
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "qlr.h"

// Settings
#define UNROLL_X 4 // hardcoded, do not change
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

// Dimensions of matrices
// A = M x N, B = N x P, C = M x N

// M and P must be multiples of 'degree of unrolling'
// e.g., degree of unrolling = 3 if every PE computes a 3x3 output chunk
// For better performance, multiple of 'systolic size' * 'degree of unrolling'
// N can be any value; N >> M, N >> P is recommended for compute-boundness

// Note that 'systolic size' and 'degree of unrolling' might be different
// based on the considered dimension (row, column)

#ifndef DIM_M
#define DIM_M (16 * 4 * 2)
#endif
#ifndef DIM_N
// inner dimension
#define DIM_N (30)
#endif
#ifndef DIM_P
#define DIM_P (16 * 4 * 2)
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
    sub_C[12] = 0;  \
    sub_C[13] = 0;  \
    sub_C[14] = 0;  \
    sub_C[15] = 0;  \
  } while(0)

#define MAC_SUBCOL_4X1(C_0, C_1, C_2, C_3, B)                                       \
  do {                                                                              \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_0)) : "r"(qlr_t0), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_1)) : "r"(qlr_t1), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_2)) : "r"(qlr_t2), "r"((B))); \
    __asm__ __volatile__("p.mac %0, %1, %2" : "+r"((C_3)) : "r"(qlr_t3), "r"((B))); \
  } while(0)

#define LOAD_SUBROW_POSTINCR(B, PTR, INCR)                \
  do {                                                    \
    __asm__ __volatile__("p.lw %0, %[incr](%[addr]!)"     \
                         : "=r"((B)), [addr] "+&r"((PTR)) \
                         : [incr] "I"((INCR))             \
                         : "memory");                     \
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
    C[((BASE_Y) + 0) * P + ((BASE_X) + 2)] = sub_C[8];  \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 2)] = sub_C[9];  \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 2)] = sub_C[10]; \
    C[((BASE_Y) + 3) * P + ((BASE_X) + 2)] = sub_C[11]; \
    C[((BASE_Y) + 0) * P + ((BASE_X) + 3)] = sub_C[12]; \
    C[((BASE_Y) + 1) * P + ((BASE_X) + 3)] = sub_C[13]; \
    C[((BASE_Y) + 2) * P + ((BASE_X) + 3)] = sub_C[14]; \
    C[((BASE_Y) + 3) * P + ((BASE_X) + 3)] = sub_C[15]; \
  } while(0)

// for faster post-addressing instructions
#define A_ROW_INCR (sizeof(int32_t) * DIM_N)
#define B_ROW_INCR (sizeof(int32_t) * DIM_P)


// row producing processing element
void systolic_rp_pe(const uint32_t row_idx,
                    const uint32_t M, const uint32_t N, const uint32_t P,
                    int32_t const *__restrict__ A) {
  // always keep output in regfile
  register int32_t sub_col_A[UNROLL_Y];

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

  // Go step-wise through the input matrix A
  for (uint32_t base_y = 0; base_y < M; base_y += UNROLL_Y * SYSTOLIC_SIZE) {
    // SYSTOLIC_SIZE - 1 because 1st col does not process C
    for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * (SYSTOLIC_SIZE - 1)) {
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

        // Push A sub-columns through the systolic array
        sub_col_A[0] = A[(shifted_y + 0) * N + 0];
        sub_col_A[1] = A[(shifted_y + 1) * N + 0];
        sub_col_A[2] = A[(shifted_y + 2) * N + 0];
        sub_col_A[3] = A[(shifted_y + 3) * N + 0];
        for (uint32_t i = 1; i < N; ++i) {
          __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t0) : "r"(sub_col_A[0]));
          sub_col_A[0] = A[(shifted_y + 0) * N + i];
          __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t1) : "r"(sub_col_A[1]));
          sub_col_A[1] = A[(shifted_y + 1) * N + i];
          __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t2) : "r"(sub_col_A[2]));
          sub_col_A[2] = A[(shifted_y + 2) * N + i];
          __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t3) : "r"(sub_col_A[3]));
          sub_col_A[3] = A[(shifted_y + 3) * N + i];
        }
        __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t0) : "r"(sub_col_A[0]));
        __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t1) : "r"(sub_col_A[1]));
        __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t2) : "r"(sub_col_A[2]));
        __asm__ __volatile__("mv %0, %1" : "=r"(qlr_t3) : "r"(sub_col_A[3]));
      }
    }
  }
}


#define COMPUTATION_NP_PE                                                                     \
  do {                                                                                        \
    MAC_SUBCOL_4X1(sub_C[0], sub_C[1], sub_C[2], sub_C[3], sub_row_B[0]);                     \
    LOAD_SUBROW_POSTINCR(sub_row_B[0], b_ptr, sizeof(int32_t));                               \
    MAC_SUBCOL_4X1(sub_C[4], sub_C[5], sub_C[6], sub_C[7], sub_row_B[1]);                     \
    LOAD_SUBROW_POSTINCR(sub_row_B[1], b_ptr, sizeof(int32_t));                               \
    MAC_SUBCOL_4X1(sub_C[8], sub_C[9], sub_C[10], sub_C[11], sub_row_B[2]);                   \
    LOAD_SUBROW_POSTINCR(sub_row_B[2], b_ptr, sizeof(int32_t));                               \
    MAC_SUBCOL_4X1(sub_C[12], sub_C[13], sub_C[14], sub_C[15], sub_row_B[3]);                 \
    LOAD_SUBROW_POSTINCR(sub_row_B[3], b_ptr, B_ROW_INCR - (UNROLL_Y - 1) * sizeof(int32_t)); \
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
    // SYSTOLIC_SIZE - 1 because 1st col does not process C
      for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * (SYSTOLIC_SIZE - 1)) {
        // Shift base_x and base_y
        shifted_x = base_x + UNROLL_X * (col_idx - 1); // -1 because 1st col does not process C
        shifted_y = base_y + UNROLL_Y * row_idx;
        // for post-increment addressing
        const int32_t *b_ptr = &B[shifted_x];

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

          // unroll first iteration of the loop to schedule the load from iteration N in iteration N-1
          LOAD_SUBROW_POSTINCR(sub_row_B[0], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[1], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[2], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[3], b_ptr, B_ROW_INCR - (UNROLL_Y - 1) * sizeof(int32_t));
          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N - 1; i++) {
            COMPUTATION_NP_PE;
          }
          // unroll last computation iteration
          MAC_SUBCOL_4X1(sub_C[0], sub_C[1], sub_C[2], sub_C[3], sub_row_B[0]);
          MAC_SUBCOL_4X1(sub_C[4], sub_C[5], sub_C[6], sub_C[7], sub_row_B[1]);
          MAC_SUBCOL_4X1(sub_C[8], sub_C[9], sub_C[10], sub_C[11], sub_row_B[2]);
          MAC_SUBCOL_4X1(sub_C[12], sub_C[13], sub_C[14], sub_C[15], sub_row_B[3]);

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  } else {
    // Execute step-wise matrix multiplication
    for (uint32_t base_y = 0; base_y < M; base_y += UNROLL_Y * SYSTOLIC_SIZE) {
    // SYSTOLIC_SIZE - 1 because 1st col does not process C
      for (uint32_t base_x = 0; base_x < P; base_x += UNROLL_X * (SYSTOLIC_SIZE - 1)) {
        // Shift base_x and base_y
        shifted_x = base_x + UNROLL_X * (col_idx - 1); // -1 because 1st col does not process C
        shifted_y = base_y + UNROLL_Y * row_idx;
        // for post-increment addressing
        const int32_t *b_ptr = &B[shifted_x];

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

          // unroll first iteration of the loop to schedule the load from iteration N in iteration N-1
          LOAD_SUBROW_POSTINCR(sub_row_B[0], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[1], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[2], b_ptr, sizeof(int32_t));
          LOAD_SUBROW_POSTINCR(sub_row_B[3], b_ptr, B_ROW_INCR - (UNROLL_Y - 1) * sizeof(int32_t));
          // Systolic matrix multiplication through MACs
          for (uint32_t i = 0; i < N - 1; i++) {
            COMPUTATION_NP_PE;
          }
          // unroll last computation iteration
          MAC_SUBCOL_4X1(sub_C[0], sub_C[1], sub_C[2], sub_C[3], sub_row_B[0]);
          MAC_SUBCOL_4X1(sub_C[4], sub_C[5], sub_C[6], sub_C[7], sub_row_B[1]);
          MAC_SUBCOL_4X1(sub_C[8], sub_C[9], sub_C[10], sub_C[11], sub_row_B[2]);
          MAC_SUBCOL_4X1(sub_C[12], sub_C[13], sub_C[14], sub_C[15], sub_row_B[3]);

          // Store values
          STORE_SUB_C(shifted_y, shifted_x);
        }
      }
    }
  }
}
