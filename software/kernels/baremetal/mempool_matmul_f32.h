// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* This library implements the matrix multiplication in multiple different ways.
 * The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 */

#include "builtins_v2.h"

void matmul_2x2_single_f32(float const *__restrict__ A,
                           float const *__restrict__ B, float *__restrict__ C,
                           uint32_t M, uint32_t N, uint32_t P) {

  for (uint32_t i = 0; i < M; i++) {
    for (uint32_t j = 0; j < P; j += 2) {
      float c00 = 0.0f;
      float c01 = 0.0f;
      float c10 = 0.0f;
      float c11 = 0.0f;
      for (uint32_t k = 0; k < N; k += 2) {
        // Explicitly load the values first to help with scheduling
        float val_a00 = A[(i + 0) * N + k + 0];
        float val_a01 = A[(i + 0) * N + k + 1];
        float val_a10 = A[(i + 1) * N + k + 0];
        float val_a11 = A[(i + 1) * N + k + 1];
        float val_b00 = B[(k + 0) * P + j + 0];
        float val_b01 = B[(k + 0) * P + j + 1];
        float val_b10 = B[(k + 1) * P + j + 0];
        float val_b11 = B[(k + 1) * P + j + 1];
        float mul00 = 0.0f;
        float mul01 = 0.0f;
        float mul10 = 0.0f;
        float mul11 = 0.0f;
        asm volatile(
            "fmadd.s %[c00], %[val_a00], %[val_b00], %[c00];"
            "fmadd.s %[c01], %[val_a00], %[val_b01], %[c01];"
            "fmadd.s %[c10], %[val_a10], %[val_b00], %[c10];"
            "fmadd.s %[c11], %[val_a10], %[val_b01], %[c11];"
            "fmadd.s %[c00], %[val_a01], %[val_b10], %[c00];"
            "fmadd.s %[c01], %[val_a01], %[val_b11], %[c01];"
            "fmadd.s %[c10], %[val_a11], %[val_b10], %[c10];"
            "fmadd.s %[c11], %[val_a11], %[val_b11], %[c11];"
            : [c00] "+&r"(c00), [c01] "+&r"(c01), [c10] "+&r"(c10),
              [c11] "+&r"(c11), [mul00] "+&r"(mul00), [mul01] "+&r"(mul01),
              [mul10] "+&r"(mul10), [mul11] "+&r"(mul11)
            : [val_a00] "r"(val_a00), [val_a01] "r"(val_a01),
              [val_a10] "r"(val_a10), [val_a11] "r"(val_a11),
              [val_b00] "r"(val_b00), [val_b01] "r"(val_b01),
              [val_b10] "r"(val_b10), [val_b11] "r"(val_b11));
      }
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
    }
  }
}

void matmul_2x2_parallel_f32(float const *__restrict__ A,
                             float const *__restrict__ B, float *__restrict__ C,
                             uint32_t M, uint32_t N, uint32_t P, uint32_t id,
                             uint32_t numThreads) {

  // Parallelize by assigning each core one row
  uint32_t const c = 8; // How many columns to split the matrix into
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);
  for (uint32_t i = 2 * (id / c); i < M; i += 2 * (numThreads / c)) {
    for (uint32_t j = c_start; j < c_end; j += 2) {
      float c00 = 0.0f;
      float c01 = 0.0f;
      float c10 = 0.0f;
      float c11 = 0.0f;
      for (uint32_t k = 0; k < N; k += 2) {
        // Explicitly load the values first to help with scheduling
        float val_a00 = A[(i + 0) * N + k + 0];
        float val_a01 = A[(i + 0) * N + k + 1];
        float val_a10 = A[(i + 1) * N + k + 0];
        float val_a11 = A[(i + 1) * N + k + 1];
        float val_b00 = B[(k + 0) * P + j + 0];
        float val_b01 = B[(k + 0) * P + j + 1];
        float val_b10 = B[(k + 1) * P + j + 0];
        float val_b11 = B[(k + 1) * P + j + 1];
        float mul00 = 0.0f;
        float mul01 = 0.0f;
        float mul10 = 0.0f;
        float mul11 = 0.0f;
        asm volatile(
            "fmadd.s %[c00], %[val_a00], %[val_b00], %[c00];"
            "fmadd.s %[c01], %[val_a00], %[val_b01], %[c01];"
            "fmadd.s %[c10], %[val_a10], %[val_b00], %[c10];"
            "fmadd.s %[c11], %[val_a10], %[val_b01], %[c11];"
            "fmadd.s %[c00], %[val_a01], %[val_b10], %[c00];"
            "fmadd.s %[c01], %[val_a01], %[val_b11], %[c01];"
            "fmadd.s %[c10], %[val_a11], %[val_b10], %[c10];"
            "fmadd.s %[c11], %[val_a11], %[val_b11], %[c11];"
            : [c00] "+&r"(c00), [c01] "+&r"(c01), [c10] "+&r"(c10),
              [c11] "+&r"(c11), [mul00] "+&r"(mul00), [mul01] "+&r"(mul01),
              [mul10] "+&r"(mul10), [mul11] "+&r"(mul11)
            : [val_a00] "r"(val_a00), [val_a01] "r"(val_a01),
              [val_a10] "r"(val_a10), [val_a11] "r"(val_a11),
              [val_b00] "r"(val_b00), [val_b01] "r"(val_b01),
              [val_b10] "r"(val_b10), [val_b11] "r"(val_b11));
        //        asm volatile(
        //          "fmul.s %[mul00], %[val_a00], %[val_b00];"
        //          "fmul.s %[mul01], %[val_a01], %[val_b10];"
        //          "fmul.s %[mul10], %[val_a00], %[val_b01];"
        //          "fmul.s %[mul11], %[val_a01], %[val_b11];"
        //          "fadd.s %[c00], %[c00], %[mul00];"
        //          "fadd.s %[c00], %[c00], %[mul01];"
        //          "fadd.s %[c01], %[c01], %[mul10];"
        //          "fadd.s %[c01], %[c01], %[mul11];"
        //          "fmul.s %[mul00], %[val_a10], %[val_b00];"
        //          "fmul.s %[mul01], %[val_a11], %[val_b10];"
        //          "fmul.s %[mul10], %[val_a10], %[val_b01];"
        //          "fmul.s %[mul11], %[val_a11], %[val_b11];"
        //          "fadd.s %[c10], %[c10], %[mul00];"
        //          "fadd.s %[c10], %[c10], %[mul01];"
        //          "fadd.s %[c11], %[c11], %[mul10];"
        //          "fadd.s %[c11], %[c11], %[mul11];"
        //          : [c00] "+&r"(c00), [c01] "+&r"(c01), [c10] "+&r"(c10),
        //          [c11] "+&r"(c11),
        //            [mul00] "+&r"(mul00), [mul01] "+&r"(mul01), [mul10]
        //            "+&r"(mul10), [mul11] "+&r"(mul11)
        //          : [val_a00] "r"(val_a00), [val_a01] "r"(val_a01), [val_a10]
        //          "r"(val_a10), [val_a11] "r"(val_a11),
        //            [val_b00] "r"(val_b00), [val_b01] "r"(val_b01), [val_b10]
        //            "r"(val_b10), [val_b11] "r"(val_b11));
      }
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
    }
  }
}

void matmul_4x2_parallel_f32vec(const float *__restrict__ pSrcA,
                                const float *__restrict__ pSrcB,
                                float *__restrict__ pDstC, uint32_t M,
                                uint32_t N, uint32_t P, uint32_t core_id,
                                uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = core_id; k < P / 2; k += numThreads) {
    for (i = 0; i < M / 4; i++) {
      float volatile sum00 = 0.0f;
      float volatile sum01 = 0.0f;
      float volatile sum10 = 0.0f;
      float volatile sum11 = 0.0f;
      float volatile sum20 = 0.0f;
      float volatile sum21 = 0.0f;
      float volatile sum30 = 0.0f;
      float volatile sum31 = 0.0f;
      for (j = 0; j < N / 2; j++) {
        float a00 = pSrcA[(i * 4) * N + (j * 2)];
        float a01 = pSrcA[(i * 4) * N + (j * 2) + 1];
        float a10 = pSrcA[(i * 4 + 1) * N + (j * 2)];
        float a11 = pSrcA[(i * 4 + 1) * N + (j * 2) + 1];
        float a20 = pSrcA[(i * 4 + 2) * N + (j * 2)];
        float a21 = pSrcA[(i * 4 + 2) * N + (j * 2) + 1];
        float a30 = pSrcA[(i * 4 + 3) * N + (j * 2)];
        float a31 = pSrcA[(i * 4 + 3) * N + (j * 2) + 1];
        float b00 = pSrcB[(j * 2) * P + (k * 2)];
        float b01 = pSrcB[(j * 2) * P + (k * 2) + 1];
        float b10 = pSrcB[(j * 2 + 1) * P + (k * 2)];
        float b11 = pSrcB[(j * 2 + 1) * P + (k * 2) + 1];
        v2h aVec0, aVec1, aVec2, aVec3;
        v2h bVec0, bVec1;
        asm volatile(
            "vfcpka.h.s %[aVec0], %[a00], %[a01];"
            "vfcpka.h.s %[aVec1], %[a10], %[a11];"
            "vfcpka.h.s %[aVec2], %[a20], %[a21];"
            "vfcpka.h.s %[aVec3], %[a30], %[a31];"
            "vfcpka.h.s %[bVec0], %[b00], %[b10];"
            "vfcpka.h.s %[bVec1], %[b01], %[b11];"
            "vfdotpex.s.h %[sum00], %[aVec0], %[bVec0];"
            "vfdotpex.s.h %[sum01], %[aVec0], %[bVec1];"
            "vfdotpex.s.h %[sum10], %[aVec1], %[bVec0];"
            "vfdotpex.s.h %[sum11], %[aVec1], %[bVec1];"
            "vfdotpex.s.h %[sum20], %[aVec2], %[bVec0];"
            "vfdotpex.s.h %[sum21], %[aVec2], %[bVec1];"
            "vfdotpex.s.h %[sum30], %[aVec3], %[bVec0];"
            "vfdotpex.s.h %[sum31], %[aVec3], %[bVec1];"
            : [sum00] "=r"(sum00), [sum01] "=r"(sum01), [sum10] "=r"(sum10),
              [sum11] "=r"(sum11), [sum20] "=r"(sum20), [sum21] "=r"(sum21),
              [sum30] "=r"(sum30), [sum31] "=r"(sum31), [aVec0] "=r"(aVec0),
              [aVec1] "=r"(aVec1), [aVec2] "=r"(aVec2), [aVec3] "=r"(aVec3),
              [bVec0] "=r"(bVec0), [bVec1] "=r"(bVec1)
            : [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10), [b11] "r"(b11),
              [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),
              [a20] "r"(a20), [a21] "r"(a21), [a30] "r"(a30), [a31] "r"(a31)
            :);
      }
      pDstC[(i * 4) * P + (k * 2)] = sum00;
      pDstC[(i * 4) * P + (k * 2 + 1)] = sum01;
      pDstC[(i * 4 + 1) * P + (k * 2)] = sum10;
      pDstC[(i * 4 + 1) * P + (k * 2 + 1)] = sum11;
      pDstC[(i * 4 + 2) * P + (k * 2)] = sum20;
      pDstC[(i * 4 + 2) * P + (k * 2 + 1)] = sum21;
      pDstC[(i * 4 + 3) * P + (k * 2)] = sum30;
      pDstC[(i * 4 + 3) * P + (k * 2 + 1)] = sum31;
    }
  }
}

///*******************************/
///* ASM CODE KERNEL START BELOW */
///*******************************/

// Define immediate values that used in asm code.
#define N3 (matrix_M - 3) * 4
#define N31 (-3 * matrix_N + 1) * 4
#define P3 (matrix_P - 3) * 4
#define P31 (-3 * matrix_N + 1) * 4

void matmul_4x4_parallel_f32(float const *__restrict__ A,
                             float const *__restrict__ B, float *__restrict__ C,
                             uint32_t M, uint32_t N, uint32_t P, uint32_t id,
                             uint32_t numThreads) {

#ifndef ASM

  /////////////////////////////
  //      Configuration      //
  /////////////////////////////
  // Parallelize by assigning each core one row
  // How many cores per window
  uint32_t c = numThreads / (M / 4);
  if (numThreads * 4 < M) {
    c = 1;
  }
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);

  // For avoiding group conflict by same tile
  // Each cores in the same tile should access to different groups
  uint32_t group_bank_nums = 512;              // MemPool = 256
  uint32_t tile_core_nums = 8;                 // MemPool = 4
  uint32_t jump_lines_A = group_bank_nums / N; // Used for i control
  uint32_t jump_lines_B = group_bank_nums / P; // Used for k control
  // Window size limit, min jump lines is 4 for MatrixA
  if (jump_lines_A < 4) {
    jump_lines_A = 4;
  }

  /////////////////////////////
  //      LOOP   OFFSET      //
  /////////////////////////////
  // Outer Loop Control, for group access port conflict
  uint32_t i_offset = jump_lines_A * (id % tile_core_nums);
  // Inner Loop Incremental Control, for group access port conflict
  uint32_t k_offset_incr = jump_lines_B * (id % tile_core_nums);
  // Inner Loop Control
  // k_offset = (Core offset) + (Window offset) + (Group offset from MatrixB)
  uint32_t k_offset = (id % c) + (2 * (id / c)) + k_offset_incr;
  // Middle Loop Control, window jump for avoiding bank conflict
  uint32_t conflict_row = (group_bank_nums * tile_core_nums) / P;
  uint32_t j_offset = (2 * (id / c)) / conflict_row;

  /////////////////////////////
  //      LOOP  CONTROL      //
  /////////////////////////////
  // Inner Round-Robin
  if (k_offset >= N) {
    k_offset = k_offset - N * (k_offset / N);
  }
  // Middle Round-Robin
  uint32_t window_in_P = (P / c) / 4;
  if (j_offset >= window_in_P) {
    j_offset = j_offset - window_in_P * (j_offset / window_in_P);
  }
  // Outer Loop Control
  uint32_t outer_loop_counter = 0;
  uint32_t outer_loop_time = M / (4 * numThreads);
  if (outer_loop_time < 1) {
    outer_loop_time = 1;
  }
  uint32_t M_partition = M / outer_loop_time;

  /////////////////////////////
  //      *LOOP  START*      //
  /////////////////////////////
  for (uint32_t i_ori = 4 * (id / c); i_ori < M;
       i_ori += 4 * (numThreads / c)) {
    outer_loop_counter += 1;
    uint32_t i = i_ori + i_offset;
    // Round-Robin control, if offset lines > M, back to the first window
    if (i >= M_partition * outer_loop_counter) {
      i = i - M_partition * (i / (M_partition * outer_loop_counter));
    }
    // Backup counter for mid-loop
    uint32_t j_offset_counter = c_start + j_offset * 4;
    uint32_t P_counter = c_end;

  Mid_loop:
    for (uint32_t j = j_offset_counter; j < P_counter; j += 4) {
      // Initialize 4x4 output tile
      float c00 = 0, c01 = 0, c02 = 0, c03 = 0;
      float c10 = 0, c11 = 0, c12 = 0, c13 = 0;
      float c20 = 0, c21 = 0, c22 = 0, c23 = 0;
      float c30 = 0, c31 = 0, c32 = 0, c33 = 0;

      // Backup the variables for restore and later use
      uint32_t k_offset_counter = k_offset;
      uint32_t N_counter = N;

    Inner_Loop:
      for (uint32_t k = k_offset_counter; k < N_counter; k += 1) {
        // Explicitly load the values first to help with scheduling
        float b0 = B[k * P + j + 0];
        float b1 = B[k * P + j + 1];
        float b2 = B[k * P + j + 2];
        float b3 = B[k * P + j + 3];
        // A could be local with scrambling
        float a0 = A[(i + 0) * N + k];
        float a1 = A[(i + 1) * N + k];
        float a2 = A[(i + 2) * N + k];
        float a3 = A[(i + 3) * N + k];
        // Compute
        c00 += a0 * b0;
        c01 += a0 * b1;
        c02 += a0 * b2;
        c03 += a0 * b3;
        c10 += a1 * b0;
        c11 += a1 * b1;
        c12 += a1 * b2;
        c13 += a1 * b3;
        c20 += a2 * b0;
        c21 += a2 * b1;
        c22 += a2 * b2;
        c23 += a2 * b3;
        c30 += a3 * b0;
        c31 += a3 * b1;
        c32 += a3 * b2;
        c33 += a3 * b3;
      }

      // Pseudo-jump code to avoid complie inner-loop twice
      // Complie twice will have scheduling issue due to register file limit.
      if (k_offset_counter > 0) {
        N_counter = k_offset;
        k_offset_counter = 0;
        goto Inner_Loop;
      }

      // Store
      C[(i + 0) * P + j + 0] = c00;
      C[(i + 0) * P + j + 1] = c01;
      C[(i + 0) * P + j + 2] = c02;
      C[(i + 0) * P + j + 3] = c03;
      C[(i + 1) * P + j + 0] = c10;
      C[(i + 1) * P + j + 1] = c11;
      C[(i + 1) * P + j + 2] = c12;
      C[(i + 1) * P + j + 3] = c13;
      C[(i + 2) * P + j + 0] = c20;
      C[(i + 2) * P + j + 1] = c21;
      C[(i + 2) * P + j + 2] = c22;
      C[(i + 2) * P + j + 3] = c23;
      C[(i + 3) * P + j + 0] = c30;
      C[(i + 3) * P + j + 1] = c31;
      C[(i + 3) * P + j + 2] = c32;
      C[(i + 3) * P + j + 3] = c33;
    }

    if (j_offset_counter != c_start) {
      P_counter = j_offset_counter;
      j_offset_counter = c_start;
      goto Mid_loop;
    }
  }

#else
  /////////////////////////////
  //      Configuration      //
  /////////////////////////////
  // Parallelize by assigning each core one row
  // How many cores per window
  uint32_t c = numThreads / (M / 4);
  if (numThreads * 4 < M) {
    c = 1;
  }
  uint32_t const c_start = (P / c) * (id % c);
  uint32_t const c_end = (P / c) * ((id % c) + 1);
  // For avoiding group conflict by same tile
  // Each cores in the same tile should access to different groups
  uint32_t group_bank_nums = 512;              // MemPool = 256
  uint32_t tile_core_nums = 8;                 // MemPool = 4
  uint32_t jump_lines_A = group_bank_nums / N; // Used for i control
  uint32_t jump_lines_B = group_bank_nums / P; // Used for k control
  // Window size limit, min jump lines is 4 for MatrixA
  if (jump_lines_A < 4) {
    jump_lines_A = 4;
  }
  /////////////////////////////
  //      LOOP   OFFSET      //
  /////////////////////////////
  // Outer Loop Control, for group access port conflict
  uint32_t i_offset = jump_lines_A * (id % tile_core_nums);
  // Inner Loop Incremental Control, for group access port conflict
  uint32_t k_offset_incr = jump_lines_B * (id % tile_core_nums);
  // Inner Loop Control
  // k_offset = (Core offset) + (Window offset) + (Group offset from MatrixB)
  uint32_t k_offset = (id % c) + (2 * (id / c)) + k_offset_incr;
  // Middle Loop Control, window jump for avoiding bank conflict
  uint32_t conflict_row = (group_bank_nums * tile_core_nums) / P;
  uint32_t j_offset = (2 * (id / c)) / conflict_row;
  /////////////////////////////
  //      LOOP  CONTROL      //
  /////////////////////////////
  // Inner Round-Robin
  if (k_offset >= N) {
    k_offset = k_offset - N * (k_offset / N);
  }
  // Middle Round-Robin
  uint32_t window_in_P = (P / c) / 4;
  if (j_offset >= window_in_P) {
    j_offset = j_offset - window_in_P * (j_offset / window_in_P);
  }
  // Outer Loop Control
  uint32_t outer_loop_counter = 0;
  uint32_t outer_loop_time = M / (4 * numThreads);
  if (outer_loop_time < 1) {
    outer_loop_time = 1;
  }
  uint32_t M_partition = M / outer_loop_time;

  /////////////////////////////
  //      *LOOP  START*      //
  /////////////////////////////
  for (uint32_t i_ori = 4 * (id / c); i_ori < M;
       i_ori += 4 * (numThreads / c)) {
    outer_loop_counter += 1;
    uint32_t i = i_ori + i_offset;
    // Round-Robin control, if offset lines > M, back to the first window
    if (i >= M_partition * outer_loop_counter) {
      i = i - M_partition * (i / (M_partition * outer_loop_counter));
    }
    // Backup counter for mid-loop
    uint32_t j_offset_counter = c_start + j_offset * 4;
    uint32_t P_counter = c_end;

  Mid_loop:
    for (uint32_t j = j_offset_counter; j < P_counter; j += 4) {
      // Address registers
      float const *addr_a_ori = &A[i * N];
      float const *addr_b_ori = &B[j];
      float const *addr_a = &A[i * N + k_offset];
      float const *addr_b = &B[k_offset * P + j];
      float const *end_b = &B[N * P + j];
      float const *addr_c = &C[i * P + j];
      register int32_t k asm("x1") = (int32_t)end_b;
      //      x12 x13 x14 x15
      //
      // x3   x16 x17 x18 x19
      // x4   x20 x21 x22 x23
      // x10  x24 x25 x26 x27
      // x11  x28 x29 x30 x31
      //
      //
      __asm__ volatile(
          ".balign 16 \n\t"
          // Outer loop: Initialize and preload. Execute this loop P times
          // TODO arrange
          "add sp, sp, -8 \n\t"
          "sw %[addr_b], 0(sp) \n\t"
          "sw %[addr_a_ori], 4(sp) \n\t"
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.lw x15, %[P_3](%[addr_b]!) \n\t" // Increment by P-3
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t" // Increment by -3N+1

          // If reach endpoint, swap address
          "bne %[addr_b], x1, init_comp \n\t"
          "lw x1, 0(sp) \n\t"
          "addi %[addr_a], %[addr_a_ori], 0 \n\t"
          "addi %[addr_b], %[addr_b_ori], 0 \n\t"
          "sw %[addr_b], 0(sp) \n\t"

          // Initial computation + prefetching
          "init_comp: \n\t"
          "fmul.s x16,  x3, x12 \n\t"
          "fmul.s x17,  x3, x13 \n\t"
          "fmul.s x18,  x3, x14 \n\t"
          "fmul.s x19,  x3, x15 \n\t"
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "fmul.s x20,  x4, x12 \n\t"
          "fmul.s x21,  x4, x13 \n\t"
          "fmul.s x22,  x4, x14 \n\t"
          "fmul.s x23,  x4, x15 \n\t"
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "fmul.s x24, x10, x12 \n\t"
          "fmul.s x25, x10, x13 \n\t"
          "fmul.s x26, x10, x14 \n\t"
          "fmul.s x27, x10, x15 \n\t"
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "fmul.s x28, x11, x12 \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "fmul.s x29, x11, x13 \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "fmul.s x30, x11, x14 \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "fmul.s %[addr_a_ori], x11, x15 \n\t" // Use addr_a_ori instead of x31
          "p.lw x15, %[P_3](%[addr_b]!) \n\t"   // Increment by P-3
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t"  // Increment by -3N+1

          // If reach endpoint, swap address
          "bne %[addr_b], x1, inner_loop \n\t"
          "sw %[addr_a_ori], 8(sp) \n\t" // backup x31
          "lw %[addr_a_ori], 4(sp) \n\t" // load back addr_a_ori
          "lw x1, 0(sp) \n\t"
          "addi %[addr_a], %[addr_a_ori], 0 \n\t"
          "addi %[addr_b], %[addr_b_ori], 0 \n\t"
          "sw %[addr_b], 0(sp) \n\t"
          "lw %[addr_a_ori], 8(sp) \n\t" // load back x31

          // Inner loop: Do this loop N times
          "inner_loop: \n\t"
          "1: \n\t"
          "fmadd.s x16,  x3, x12, x16 \n\t"
          "fmadd.s x17,  x3, x13, x17 \n\t"
          "fmadd.s x20,  x4, x12, x20 \n\t"
          "fmadd.s x21,  x4, x13, x21 \n\t"
          "fmadd.s x18,  x3, x14, x18 \n\t"
          "fmadd.s x22,  x4, x14, x22 \n\t"
          "fmadd.s x19,  x3, x15, x19 \n\t"
          "p.lw  x3, %[N](%[addr_a]!) \n\t"
          "fmadd.s x23,  x4, x15, x23 \n\t"
          "p.lw  x4, %[N](%[addr_a]!) \n\t"
          "fmadd.s x24, x10, x12, x24 \n\t"
          "fmadd.s x28, x11, x12, x28 \n\t"
          "p.lw x12, 4(%[addr_b]!) \n\t"
          "fmadd.s x25, x10, x13, x25 \n\t"
          "fmadd.s x29, x11, x13, x29 \n\t"
          "p.lw x13, 4(%[addr_b]!) \n\t"
          "fmadd.s x26, x10, x14, x26 \n\t"
          "fmadd.s x30, x11, x14, x30 \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "fmadd.s x27, x10, x15, x27 \n\t"
          "fmadd.s %[addr_a_ori], x11, x15, %[addr_a_ori] \n\t"
          "p.lw x15, %[P_3](%[addr_b]!) \n\t" // Increment by P-3
          "p.lw x10, %[N](%[addr_a]!) \n\t"
          "p.lw x11, %[N3_1](%[addr_a]!) \n\t" // Increment by -3N+1
          "bne %[addr_b], x1, 1b \n\t"

          // Case1: Loop done if k_offset = 0
          // Case2: Loop done when 2nd time to here
          // Case3: If reach endpoint, swap address
          "lw %[addr_b], 0(sp) \n\t"
          "beq %[addr_b_ori], %[addr_b], store \n\t"
          "sw %[addr_a_ori], 8(sp) \n\t" // backup x31
          "lw %[addr_a_ori], 4(sp) \n\t" // load back addr_a_ori
          "addi x1, %[addr_b], 0 \n\t"
          "addi %[addr_a], %[addr_a_ori], 0 \n\t"
          "addi %[addr_b], %[addr_b_ori], 0 \n\t"
          "sw %[addr_b], 0(sp) \n\t"
          "lw %[addr_a_ori], 8(sp) \n\t" // load back x31
          "j 1b \n\t"

          // Loop done store
          "store: \n\t"
          "fmadd.s x16,  x3, x12, x16 \n\t"
          "fmadd.s x17,  x3, x13, x17 \n\t"
          "fmadd.s x18,  x3, x14, x18 \n\t"
          "p.sw x16, 4(%[addr_c]!) \n\t"
          "fmadd.s x19,  x3, x15, x19 \n\t"
          "p.sw x17, 4(%[addr_c]!) \n\t"
          "fmadd.s x20,  x4, x12, x20 \n\t"
          "p.sw x18, 4(%[addr_c]!) \n\t"
          "fmadd.s x21,  x4, x13, x21 \n\t"
          "p.sw x19, %[P_3](%[addr_c]!) \n\t"
          "fmadd.s x22,  x4, x14, x22 \n\t"
          "p.sw x20, 4(%[addr_c]!) \n\t"
          "fmadd.s x23,  x4, x15, x23 \n\t"
          "p.sw x21, 4(%[addr_c]!) \n\t"
          "fmadd.s x24, x10, x12, x24 \n\t"
          "p.sw x22, 4(%[addr_c]!) \n\t"
          "fmadd.s x25, x10, x13, x25 \n\t"
          "p.sw x23, %[P_3](%[addr_c]!) \n\t"
          "fmadd.s x26, x10, x14, x26 \n\t"
          "p.sw x24, 4(%[addr_c]!) \n\t"
          "fmadd.s x27, x10, x15, x27 \n\t"
          "p.sw x25, 4(%[addr_c]!) \n\t"
          "fmadd.s x28, x11, x12, x28 \n\t"
          "p.sw x26, 4(%[addr_c]!) \n\t"
          "fmadd.s x29, x11, x13, x29 \n\t"
          "p.sw x27, %[P_3](%[addr_c]!) \n\t"
          "fmadd.s x30, x11, x14, x30 \n\t"
          "p.sw x28, 4(%[addr_c]!) \n\t"
          "fmadd.s %[addr_a_ori], x11, x15, %[addr_a_ori] \n\t"
          "p.sw x29, 4(%[addr_c]!) \n\t"
          "p.sw x30, 4(%[addr_c]!) \n\t"
          "p.sw %[addr_a_ori], %[P_3](%[addr_c]!) \n\t"
          "add sp, sp, 8 \n\t"
          : [addr_a] "+&r"(addr_a), [addr_b] "+&r"(addr_b),
            [addr_c] "+&r"(addr_c), [addr_a_ori] "+&r"(addr_a_ori),
            [addr_b_ori] "+&r"(addr_b_ori) // Outputs
          : [N3_1] "r"(N31), [P_3] "I"(P3), [x1] "r"(k),
            [N] "I"(matrix_N * 4) // Inputs
          : "x3", "x4", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17",
            "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",
            "x27", "x28", "x29", "x30", "memory"); // Cbber
    }
    if (j_offset_counter != c_start) {
      P_counter = j_offset_counter;
      j_offset_counter = c_start;
      goto Mid_loop;
    }
  }

#endif
}
