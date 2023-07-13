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

// Author: Sergio Mazzola, ETH Zurich
//         Samuel Riedel, ETH Zurich

/*
 * X is an MxN matrix, W is a 3x3 matrix and Y is an MxN matrix
 * Y = conv2d(X, W), X is padded with zeros to compute Y's halo
 *
 * All cores are connected in a chain-like systolic array. Each computing PE
 * receives 5 rows of X and computes 3 rows of Y.
 * In each PE, to maximize the data reuse of each loaded element of X's rows, 3
 * 3x3 kernels for each row are computed at the same time, column by column, in a
 * pipelined, interleaved fashion.
 *
 * The systolic chain topology maximizes the systolic links between cores of the
 * same local tile and local group.
 * To avoid deep queue dependencies, the systolic array is divided into
 * multiple chains of PEs. The front PE of each chain (i.e., 'mover PE') directly
 * accesses memory to load 2 rows of X. The inner PEs (i.e., 'computing PEs') pop
 * rows -1 and 0 from the previous PE, load row 1, 2, and 3 directly from memory
 * with load instructions, and push rows 2 and 3 to the subsequent PE. The last PE
 * of each chain is a computing PE which does not push to anything.
 *
 * Before the systolic computation, each PE laods the 3x3 weight kernel directly
 * from memory and stores it in its register file.
 *
 * NOTE: M and N must be at least 3. The kernel size is hardcoded to 3x3.
 *       Due to the 3-row unrolling, M must be a multiple of 3.
 *
 * Schematic dataflow of each computing PE:
 * ----------------------------------------------------
 * row -1 -> from qlr_t0
 * row  0 -> from qlr_t1 (same id as row_base_assign*i)
 * row  1 -> loaded from memory
 * row  2 -> loaded from memory (and pushed to qlr_t2)
 * row  3 -> loaded from memory (and pushed to qlr_t3)
 * ----------------------------------------------------
 * rows -1,0,1 -> 1st output row
 * rows  0,1,2 -> 2nd output row
 * rows  1,2,3 -> 3rd output row
 * ----------------------------------------------------
 */

#include "alloc.h"
#include "printf.h"
#include "synchronization.h"
#include "qlr.h"

/* Settings */
#define PRINT_ROW_PROC 1

/* Dimensions of matrices */
// X,Y = MxN; kernel = KxK
// rows
#ifndef DIM_M
#define DIM_M 3*240
#endif
// columns
#ifndef DIM_N
#define DIM_N 84
#endif
// Kernel dimension
#define K 3 // hardcoded, do not change

/* Convolution configuration */
// Repetition count
#ifndef REP_COUNT
#define REP_COUNT 1
#endif
// Systolic length (must be divisor of NUM_CORES)
#ifndef SYSTOLIC_LENGTH
#define SYSTOLIC_LENGTH 16
#endif
// How many pipelined convolutions per row, per PE
#define CONV_UNROLL (K) // hardcoded, do not change
// How many rows per PE
#define ROWS_UNROLL 3 // hardcoded, do not change

/* Array of queue pointers in row-major order */
uint32_t *queues_x_0[NUM_CORES];
uint32_t *queues_x_1[NUM_CORES];

/*
 * Initialize systolic array
 */
void systolic_init(uint32_t const *core_map) {
  // Create systolic array via queues
  uint32_t core_id;
  uint32_t offset;
  // We want all cores connected in a chain, each one taking care of a row
  // Serially connecting all cores in a chain with the order based on their
  // core_id maximizes the systolic links going through the same tile and
  // the same group
  for (uint32_t i = 0; i < NUM_CORES; i++) {
    core_id = core_map[i];
    offset = core_id * NUM_QUEUES_PER_CORE;
    queues_x_0[i] = (uint32_t *)(offset + 0);
    queues_x_1[i] = (uint32_t *)(offset + 1);
    // only 2 queues used (but you want to always use each core's
    // local memory banks, so keep the offset multiple of NUM_QUEUES_PER_CORE)
  }
}


// QLR CSR addresses
#define DEFINE_QLR_CFG_CSR(N)                                 \
  volatile uint32_t *qlr_cfg_t##N = (uint32_t *)QLR_CFG_T##N

// Print through CSR
#define PRINT_ROW_ID(r) \
  write_csr(0, (r))

#define LOAD_ZERO_PADDING(qlr) \
  __asm__ __volatile__("li %0, 0" : "=r"((qlr_t1)))


/*
 * Front core of the systolic convolution chain
 */
void systolic_conv_front(const uint32_t core_id, const uint32_t chain_id,
                         const uint32_t num_chains, const uint32_t num_cores,
                         const uint32_t num_rows, const uint32_t num_cols,
                         int32_t const *__restrict__ X, const uint32_t rep_count) {
  uint32_t qpush_reqs;
  uint32_t row, col;
  // as we loose 1 computing PE for each chain
  const uint32_t computing_cores = num_cores - num_chains;

  /* Row assigned to this PE */
  // every chain has 1 non-processing core (frontal cores), i.e., to get the
  // ID of the actually processed row we have to subtract one more for each
  // chain. This is the same of subtracting chain_id
  uint32_t row_base_assign = core_id - chain_id;

  // pointers to QLR config
  DEFINE_QLR_CFG_CSR(1);
  DEFINE_QLR_CFG_CSR(2);

  /* Calculate queue requests */
  // "remaining_rows / tot_processing_cores" is the number of times this PE
  // has to let a whole row of input matrix pass through the systolic array
  if (row_base_assign < num_rows / ROWS_UNROLL) {
    // (tot rows) - (rows assigned so far) + (-1 for ceil before div)
    qpush_reqs = (((num_rows / ROWS_UNROLL - row_base_assign - 1 // number of remaining rows
                 ) / (computing_cores)             // actual number of computing cores
                 ) + 1                             // +1 for ceil after div
                 ) * num_cols;                     // elements per row
  } else {
    return;
  }

  // Configure QLRs
  qlr_cfg_t1[QLR_CFG_REQ]   = (uint32_t)qpush_reqs;
  qlr_cfg_t1[QLR_CFG_OADDR] = (uint32_t)queues_x_0[core_id + 1];
  qlr_cfg_t2[QLR_CFG_REQ]   = (uint32_t)qpush_reqs;
  qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_x_1[core_id + 1];

  for (uint32_t rep = 0; rep < rep_count; rep++) {
    // Set row
    row = row_base_assign * ROWS_UNROLL;

    // Start QLRs
    qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
    qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_OQLR;

    /* SPECIAL CASE */
    // Very first row (i.e., load zero padding for halo computation)
    if (row == 0) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      for (col = 0; col < num_cols; col++) {
        // Load x vector
        LOAD_ZERO_PADDING(qlr_t1);
        qlr_t2 = X[col];
      }

      // Increment row
      row = computing_cores * ROWS_UNROLL; // row is 0, so same as incrementing
    }

    /* INNER ROWS (including last) */
    // Execute row-wise systolic 2d convolution
    while (row < num_rows) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      for (col = 0; col < num_cols; col++) {
        // Load x vector
        qlr_t1 = X[(row - 1) * num_cols + col];
        qlr_t2 = X[(row + 0) * num_cols + col];
      }

      // Increment row
      row += computing_cores * ROWS_UNROLL;
    }
  }
}

// Load 1 matrix element with post-increment addressing
#define LOAD_POSTINCR(DEST, PTR, INCR)                      \
  __asm__ __volatile__("p.lw %0, %[incr](%[addr]!)"         \
                        : "=r"((DEST)), [addr] "+&r"((PTR)) \
                        : [incr] "I"((INCR))                \
                        : "memory")

// Let the compiler compute the increment for loads, for higher performance
#define COL_INCR (DIM_N * sizeof(int32_t))

#define OP_ACC_QLR_WEIGHT(op, accum_col, qlr, weight) \
  __asm__ __volatile__(op" %0, %1, %2": "+r"((accum_col)): "r"((qlr)), "r"((weight)))


// Row-wise MACs with weights
#define CONV_KERNEL_STAGE_FULL(init, middle, last)                                  \
  do {                                                                              \
    /* MACs with 1st row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)], qlr_t0, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)], qlr_t0, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[0][(init)], qlr_t0, weights[0][0]); \
    /* MACs with 1st row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)], qlr_t1, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)], qlr_t1, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[1][(init)], qlr_t1, weights[0][0]); \
    /* MACs with 1st row of weights (3rd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(last)],   in_0, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][(middle)],   in_0, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[2][(init)],   in_0, weights[0][0]); \
    /* MACs with 2nd row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)], qlr_t1, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)], qlr_t1, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(init)], qlr_t1, weights[1][0]); \
    /* MACs with 2nd row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)],   in_0, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)],   in_0, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(init)],   in_0, weights[1][0]); \
    /* MACs with 1st row of weights (3rd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(last)], qlr_t2, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][(middle)], qlr_t2, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(init)], qlr_t2, weights[1][0]); \
    /* MACs with 3rd row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)],   in_0, weights[2][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)],   in_0, weights[2][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(init)],   in_0, weights[2][0]); \
    /* MACs with 3rd row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)], qlr_t2, weights[2][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)], qlr_t2, weights[2][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(init)], qlr_t2, weights[2][0]); \
    /* MACs with 1st row of weights (3rd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(last)], qlr_t3, weights[2][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][(middle)], qlr_t3, weights[2][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(init)], qlr_t3, weights[2][0]); \
  } while (0)


#define CONV_KERNEL_STAGE_HALO(init, middle, last)                                  \
  do {                                                                              \
    /* MACs with 1st row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)], qlr_t0, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)], qlr_t0, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[0][(init)], qlr_t0, weights[0][0]); \
    /* MACs with 1st row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)], qlr_t1, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)], qlr_t1, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[1][(init)], qlr_t1, weights[0][0]); \
    /* MACs with 1st row of weights (3rd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(last)],   in_0, weights[0][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][(middle)],   in_0, weights[0][1]); \
    OP_ACC_QLR_WEIGHT(  "mul",   kernel_acc_col[2][(init)],   in_0, weights[0][0]); \
    /* MACs with 2nd row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)], qlr_t1, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)], qlr_t1, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(init)], qlr_t1, weights[1][0]); \
    /* MACs with 2nd row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)],   in_0, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)],   in_0, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(init)],   in_0, weights[1][0]); \
    /* MACs with 1st row of weights (3rd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(last)], qlr_t2, weights[1][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][(middle)], qlr_t2, weights[1][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[2][(init)], qlr_t2, weights[1][0]); \
    /* MACs with 3rd row of weights (1st output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(last)],   in_0, weights[2][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][(middle)],   in_0, weights[2][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[0][(init)],   in_0, weights[2][0]); \
    /* MACs with 3rd row of weights (2nd output row) */                             \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(last)], qlr_t2, weights[2][2]); \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][(middle)], qlr_t2, weights[2][1]); \
    OP_ACC_QLR_WEIGHT("p.mac",   kernel_acc_col[1][(init)], qlr_t2, weights[2][0]); \
  } while (0)


#define ROW_BULK_COMPUTATION                                                                                         \
  do {                                                                                                               \
    /* POPULATE */                                                                                                   \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                           \
    /* MACs with 1st row of weights (1st output row) */                                                              \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][1], qlr_t0, weights[0][2]); /* dummy (0, 0, X[i,0]) */              \
    in_0   = X[(row + 1) * num_cols];                                        /* Re-ordered load (optimization) */    \
    qlr_t2 = X[(row + 2) * num_cols];                                                                                \
    qlr_t3 = X[(row + 3) * num_cols];                                                                                \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][2], qlr_t0, weights[0][1]); /* halo (0, X[i,0], X[i,1]) */          \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][0], qlr_t0, weights[0][0]); /* kernel_0 (X[i,0], X[i,1], X[i,2]) */ \
    /* MACs with 1st row of weights (2nd output row) */                                                              \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][1], qlr_t1, weights[0][2]);                                         \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][2], qlr_t1, weights[0][1]);                                         \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][0], qlr_t1, weights[0][0]);                                         \
    /* MACs with 1st row of weights (3rd output row) */                                                              \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][1],   in_0, weights[0][2]);                                         \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][2],   in_0, weights[0][1]);                                         \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][0],   in_0, weights[0][0]);                                         \
    /* MACs with 2nd row of weights (1st output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][1], qlr_t1, weights[1][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][2], qlr_t1, weights[1][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][0], qlr_t1, weights[1][0]);                                         \
    /* MACs with 2nd row of weights (2nd output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][1],   in_0, weights[1][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][2],   in_0, weights[1][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][0],   in_0, weights[1][0]);                                         \
    /* MACs with 2nd row of weights (3rd output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][1], qlr_t2, weights[1][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][2], qlr_t2, weights[1][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][0], qlr_t2, weights[1][0]);                                         \
    /* MACs with 3rd row of weights (1st output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][1],   in_0, weights[2][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][2],   in_0, weights[2][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][0],   in_0, weights[2][0]);                                         \
    /* MACs with 3rd row of weights (2nd output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][1], qlr_t2, weights[2][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][2], qlr_t2, weights[2][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][0], qlr_t2, weights[2][0]);                                         \
    /* MACs with 3rd row of weights (3rd output row) */                                                              \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][1], qlr_t3, weights[2][2]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][2], qlr_t3, weights[2][1]);                                         \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][0], qlr_t3, weights[2][0]);                                         \
                                                                                                                     \
    /* CONVOLUTION BURST */                                                                                          \
    /* Compute 3 3x3 kernels at a time in a interleaved, pipelined way, to maximize                                  \
    * data reuse with the 3x1 column pushed at each cycle through QLRs.                                              \
    * At each cycle, for each output row, one kernel will be computing its 3rd col,                                  \
    * hence finishing and being stored. One other kernel will be at its second col,                                  \
    * and another, last, one will be at its first col, being reset with a "mul"                                      \
    * instead of "p.mac"                                                                                             \
    */                                                                                                               \
    for (col = 1; col < num_cols - 2; col += K) {                                                                    \
      /* ITERATION 0 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 0];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                                               \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */                    \
      /* ITERATION 1 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 1];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 1];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 1];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(2, 1, 0);                                                                               \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */                    \
      /* ITERATION 2 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 2];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 2];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 2];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(0, 2, 1);                                                                               \
      Y[row * num_cols + col + 1] = kernel_acc_col[0][1];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col + 1] = kernel_acc_col[1][1]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col + 1] = kernel_acc_col[2][1]; /* store finished accumulation */                    \
    }                                                                                                                \
                                                                                                                     \
    /* CONVOLUTION REMAINDER */                                                                                      \
    if (col == num_cols - 2) {                                                                                       \
      /* ITERATION 0 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 0];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                                               \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */                    \
      /* ITERATION 1 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 1];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 1];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 1];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(2, 1, 0);                                                                               \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */                    \
      /* Store partial accumulation (zero-padding) */                                                                \
      Y[row * num_cols + col + 1] = kernel_acc_col[0][1];                                                            \
      Y[(row + 1) * num_cols + col + 1] = kernel_acc_col[1][1];                                                      \
      Y[(row + 2) * num_cols + col + 1] = kernel_acc_col[2][1];                                                      \
                                                                                                                     \
    } else if (col == num_cols - 1) {                                                                                \
      /* ITERATION 0 */                                                                                              \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                                    \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                                    \
      qlr_t3 = X[(row + 3) * num_cols + col + 0];                                                                    \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                                         \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                                               \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */                    \
      /* Store partial accumulation (zero-padding) */                                                                \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */                    \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */                    \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */                    \
    } else {                                                                                                         \
      /* Store partial accumulation (zero-padding) */                                                                \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];                                                            \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2];                                                      \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2];                                                      \
    }                                                                                                                \
  } while (0)                                                                                                        \


#define ROW_LAST_COMPUTATION                                                                      \
  do {                                                                                            \
    /* SPECIAL CASE */                                                                            \
    /* Last row: convolution with only the two upper weight rows: required for halo               \
    * computation, as it is equivalent to convolution with last row of zeros                      \
    */                                                                                            \
                                                                                                  \
    /* POPULATE */                                                                                \
    __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                        \
    /* MACs with 1st row of weights (1st output row) */                                           \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][1], qlr_t0, weights[0][2]);                      \
    in_0   = X[(row + 1) * num_cols]; /* Re-ordered load (optimization) */                        \
    qlr_t2 = X[(row + 2) * num_cols];                                                             \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][2], qlr_t0, weights[0][1]);                      \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[0][0], qlr_t0, weights[0][0]);                      \
    /* MACs with 1st row of weights (2nd output row) */                                           \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][1], qlr_t1, weights[0][2]);                      \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][2], qlr_t1, weights[0][1]);                      \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[1][0], qlr_t1, weights[0][0]);                      \
    /* MACs with 1st row of weights (3rd output row) */                                           \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][1],   in_0, weights[0][2]);                      \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][2],   in_0, weights[0][1]);                      \
    OP_ACC_QLR_WEIGHT(  "mul", kernel_acc_col[2][0],   in_0, weights[0][0]);                      \
    /* MACs with 2nd row of weights (1st output row) */                                           \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][1], qlr_t1, weights[1][2]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][2], qlr_t1, weights[1][1]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][0], qlr_t1, weights[1][0]);                      \
    /* MACs with 2nd row of weights (2nd output row) */                                           \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][1],   in_0, weights[1][2]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][2],   in_0, weights[1][1]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][0],   in_0, weights[1][0]);                      \
    /* MACs with 2nd row of weights (3rd output row) */                                           \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][1], qlr_t2, weights[1][2]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][2], qlr_t2, weights[1][1]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[2][0], qlr_t2, weights[1][0]);                      \
    /* MACs with 3rd row of weights (1st output row) */                                           \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][1],   in_0, weights[2][2]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][2],   in_0, weights[2][1]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[0][0],   in_0, weights[2][0]);                      \
    /* MACs with 3rd row of weights (2nd output row) */                                           \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][1], qlr_t2, weights[2][2]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][2], qlr_t2, weights[2][1]);                      \
    OP_ACC_QLR_WEIGHT("p.mac", kernel_acc_col[1][0], qlr_t2, weights[2][0]);                      \
                                                                                                  \
    for (col = 1; col < num_cols - 2; col += K) {                                                 \
      /* ITERATION 0 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                            \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */ \
      /* ITERATION 1 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 1];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 1];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(2, 1, 0);                                                            \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */ \
      /* ITERATION 2 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 2];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 2];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(0, 2, 1);                                                            \
      Y[row * num_cols + col + 1] = kernel_acc_col[0][1];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col + 1] = kernel_acc_col[1][1]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col + 1] = kernel_acc_col[2][1]; /* store finished accumulation */ \
    }                                                                                             \
                                                                                                  \
    /* CONVOLUTION REMAINDER */                                                                   \
    if (col == num_cols - 2) {                                                                    \
      /* ITERATION 0 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                            \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */ \
      /* ITERATION 1 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 1];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 1];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(2, 1, 0);                                                            \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */ \
      /* Store partial accumulation (zero-padding) */                                             \
      Y[row * num_cols + col + 1] = kernel_acc_col[0][1];                                         \
      Y[(row + 1) * num_cols + col + 1] = kernel_acc_col[1][1];                                   \
      Y[(row + 2) * num_cols + col + 1] = kernel_acc_col[2][1];                                   \
                                                                                                  \
    } else if (col == num_cols - 1) {                                                             \
      /* ITERATION 0 */                                                                           \
      in_0   = X[(row + 1) * num_cols + col + 0];                                                 \
      qlr_t2 = X[(row + 2) * num_cols + col + 0];                                                 \
      __asm__ __volatile__("" : "=r"(qlr_t0), "=r"(qlr_t1));                                      \
      CONV_KERNEL_STAGE_FULL(1, 0, 2);                                                            \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2]; /* store finished accumulation */ \
      /* Store partial accumulation (zero-padding) */                                             \
      Y[row * num_cols + col + 0] = kernel_acc_col[0][0];       /* store finished accumulation */ \
      Y[(row + 1) * num_cols + col + 0] = kernel_acc_col[1][0]; /* store finished accumulation */ \
      Y[(row + 2) * num_cols + col + 0] = kernel_acc_col[2][0]; /* store finished accumulation */ \
    } else {                                                                                      \
      /* Store partial accumulation (zero-padding) */                                             \
      Y[row * num_cols + col - 1] = kernel_acc_col[0][2];                                         \
      Y[(row + 1) * num_cols + col - 1] = kernel_acc_col[1][2];                                   \
      Y[(row + 2) * num_cols + col - 1] = kernel_acc_col[2][2];                                   \
    }                                                                                             \
  } while (0)                                                                                     \

/*
 * Inner cores of the systolic convolution chain
 */
void systolic_conv_mid(const uint32_t core_id, const uint32_t chain_id, const uint32_t num_chains, const uint32_t num_cores,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y,
                       const uint32_t rep_count) {
  uint32_t qpopush_reqs;
  uint32_t row, col;
  // as we loose 1 computing PE for each chain
  const uint32_t computing_cores = num_cores - num_chains;

  int32_t weights[K][K];
  /* Column accumulator for each kernel */
  // we perform the convolution for each kernel in a column-interleaved fashion
  // so a number of accumulator equal to the kernel size is required
  register int32_t kernel_acc_col[ROWS_UNROLL][K] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  register int32_t in_0;

  // Load weights
  for (uint32_t y = 0; y < K; y++)
    for (uint32_t x = 0; x < K; x++)
      weights[y][x] = W[y * K + x];

  /* Row assigned to this PE */
  // same of frontal cores but subtract 1 more, to
  // compensate for the non-processing frontal cores
  uint32_t row_base_assign = core_id - (chain_id + 1);

  // pointers to QLR config
  DEFINE_QLR_CFG_CSR(0);
  DEFINE_QLR_CFG_CSR(1);
  DEFINE_QLR_CFG_CSR(2);
  DEFINE_QLR_CFG_CSR(3);

  /* Calculate queue requests */
  if (row_base_assign == num_rows / ROWS_UNROLL - 1) {
    // special case: kernel is at the last row and num_rows does not wrap around computing_cores
    qpopush_reqs = 0;
  } else if (row_base_assign < num_rows / ROWS_UNROLL - 1) {
    // (tot rows) - (rows assigned so far) + (-1 for ceil before div) + (-1 in case it's last row)
    qpopush_reqs = (((num_rows / ROWS_UNROLL - row_base_assign - 1 - 1 // number of remaining rows
                   ) / computing_cores                                 // actual number of processing cores
                   ) + 1                                               // +1 for ceil after div
                   ) * num_cols;                                       // elements per row
  } else {
    return;
  }

  // NOTE: We need -1 to trick the ceil operation into rounding down in case this
  // mid PE is processing the last row. This is because, when the last row is processed
  // the QLRs must be configured only to IQLR, otherwise a deadlock occurs.
  // QLRs cannot be re-configured unless they finished the programmed requests, hence we
  // need to configure them for one less row and re-configure them to process one further
  // row as IQLR just before the last matrix row is processed.

  /* Configure QLRs */
  if (qpopush_reqs != 0) {
    // row_base_assign - 1 (pop from previous PE)
    qlr_cfg_t0[QLR_CFG_REQ]   = (uint32_t)qpopush_reqs;
    qlr_cfg_t0[QLR_CFG_RF]    = 1 * K; // read each value "1 row * K cols" times
    qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_x_0[core_id];
    // row_base_assign (pop from previous PE)
    qlr_cfg_t1[QLR_CFG_REQ]   = (uint32_t)qpopush_reqs;
    qlr_cfg_t1[QLR_CFG_RF]    =  2 * K; // read each value "2 rows * K cols" times
    qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_x_1[core_id];
    // row_base_assign + 1 (load from memory + push into next)
    qlr_cfg_t2[QLR_CFG_REQ]   = (uint32_t)qpopush_reqs;
    qlr_cfg_t2[QLR_CFG_OADDR] = (uint32_t)queues_x_0[core_id + 1];
    // row_base_assign + 2 (load from memory + push into next)
    qlr_cfg_t3[QLR_CFG_REQ]   = (uint32_t)qpopush_reqs;
    qlr_cfg_t3[QLR_CFG_OADDR] = (uint32_t)queues_x_1[core_id + 1];
  }

  for (uint32_t rep = 0; rep < rep_count; rep++) {
    // Start QLRs
    qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
    qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
    qlr_cfg_t2[QLR_CFG_TYPE] = QLR_TYPE_OQLR;
    qlr_cfg_t3[QLR_CFG_TYPE] = QLR_TYPE_OQLR;

    // Execute row-wise systolic 2d convolution
    for (row = row_base_assign * ROWS_UNROLL; row < num_rows - ROWS_UNROLL; row += computing_cores * ROWS_UNROLL) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      ROW_BULK_COMPUTATION;
    }

    // Special case: last row
    if (row == num_rows - ROWS_UNROLL) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      /* Reconfigure only QLRs t0 and t1 for special case (no OQLRs) */
      // Setting QLR type == re-starting QLR, so we have to make sure
      // we are asking for only one more row (i.e., num_cols requests)
      qlr_cfg_t0[QLR_CFG_REQ]   = (uint32_t)num_cols;
      qlr_cfg_t0[QLR_CFG_RF]    = 1 * K;
      qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_x_0[core_id];
      qlr_cfg_t1[QLR_CFG_REQ]   = (uint32_t)num_cols;
      qlr_cfg_t1[QLR_CFG_RF]    = 2 * K;
      qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_x_1[core_id];
      // Start with new config for very last row
      qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
      qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;

      ROW_LAST_COMPUTATION;
    }
  }
}


/*
 * Ending core of the systolic convolution chain
 */
void systolic_conv_end(const uint32_t core_id, const uint32_t chain_id, const uint32_t num_chains, const uint32_t num_cores,
                       const uint32_t num_rows, const uint32_t num_cols,
                       int32_t const *__restrict__ X,
                       int32_t const *__restrict__ W, int32_t *__restrict__ Y,
                       const uint32_t rep_count) {
  uint32_t qpop_reqs;
  uint32_t row, col;
  const uint32_t computing_cores = num_cores - num_chains;

  int32_t weights[K][K];
  /* Column accumulator for each kernel */
  register int32_t kernel_acc_col[ROWS_UNROLL][K] = {{0, 0, 0}, {0, 0, 0}, {0, 0, 0}};
  register int32_t in_0;

  // Load weights
  for (uint32_t y = 0; y < K; y++)
    for (uint32_t x = 0; x < K; x++)
      weights[y][x] = W[y * K + x];

  /* Row assigned to this PE */
  uint32_t row_base_assign = core_id - (chain_id + 1);

  // pointers to QLR config
  DEFINE_QLR_CFG_CSR(0);
  DEFINE_QLR_CFG_CSR(1);

  // Calculate queue requests
  if (row_base_assign < num_rows / ROWS_UNROLL) {
    // (tot rows) - (rows assigned so far) + (-1 for ceil before div)
    qpop_reqs = (((num_rows / ROWS_UNROLL - row_base_assign - 1 // number of remaining rows
                ) / computing_cores                             // actual number of processing cores
                ) + 1                                           // +1 for ceil after div
                ) * num_cols;                                   // elements per row
  } else {
    return;
  }

  /* Configure QLRs */
  // row_base_assign - 1 (pop from previous PE)
  qlr_cfg_t0[QLR_CFG_REQ]   = (uint32_t)qpop_reqs;
  qlr_cfg_t0[QLR_CFG_RF]    = 1 * K; // read each value "1 row * K cols" times
  qlr_cfg_t0[QLR_CFG_IADDR] = (uint32_t)queues_x_0[core_id];
  // row_base_assign (pop from previous PE)
  qlr_cfg_t1[QLR_CFG_REQ]   = (uint32_t)qpop_reqs;
  qlr_cfg_t1[QLR_CFG_RF]    =  2 * K; // read each value "2 rows * K cols" times
  qlr_cfg_t1[QLR_CFG_IADDR] = (uint32_t)queues_x_1[core_id];

  for (uint32_t rep = 0; rep < rep_count; rep++) {
    // Start QLRs
    qlr_cfg_t0[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
    qlr_cfg_t1[QLR_CFG_TYPE] = QLR_TYPE_IQLR;
    // OQLR qlr_t2 not required as this is the last PE in the chain:
    // only loading row+1 for itself

    // Execute row-wise systolic 2d convolution
    for (row = row_base_assign * ROWS_UNROLL; row < num_rows - ROWS_UNROLL; row += ROWS_UNROLL * computing_cores) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      ROW_BULK_COMPUTATION;
    }

    // Special case: last row
    if (row == num_rows - ROWS_UNROLL) {
      #if PRINT_ROW_PROC
      PRINT_ROW_ID(row);
      #endif

      ROW_LAST_COMPUTATION;
    }
  }
}
