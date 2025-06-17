// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Bowen Wang <bowwang@iis.ethz.ethz.ch>
//         Yinrong Li <yinrli@student.ethz.ch>

/* This library implements the 4x4 unroll matrix multiplication.
 * The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = A x B
 */

/*
------ Mode Selection ------
Basic:      C =  A x B
Transpose:  C =  A x B_T
Accumulate: C += A x B
*/

#include <stdint.h>
#include <string.h>
#include "printf.h"
#include "builtins_v2.h"
/* 
Desc: MatMul 4x4 Unroll Kernel with asm implementation
@inp: (float *)  A, B        Pointer to the input matrices
@inp: (float *)  C           Pointer to the output matrix
@inp: (uint32_t) M, N, P     MatMul Dimensions
@inp: (uint32_t) id          Core_id
@inp: (uint32_t) numThreads
@inp: (uint32_t) c_split     Number of cores assigned to every 4 rows in Matrix C  
*/
void matmul_4x4_parallel_f16p_asm (float const *__restrict__ A, float const *__restrict__ B, float *__restrict__ C,
										 uint32_t M, uint32_t N, uint32_t P, uint32_t id, uint32_t numThreads, uint32_t c_split){
	
	uint32_t const c = c_split;
	uint32_t const c_start = (P / c) * (id % c);
	uint32_t const c_end = (P / c) * ((id % c) + 1);
	for (uint32_t i = 4 * (id / c); i < M; i += 4 * (numThreads / c)) {
	    for (uint32_t j = c_start; j < c_end; j += 4) {

	      // Initialization
	      float volatile sum00 = 0.0f;
	      float volatile sum01 = 0.0f;
	      float volatile sum02 = 0.0f;
	      float volatile sum03 = 0.0f;

	      float volatile sum10 = 0.0f;
	      float volatile sum11 = 0.0f;
	      float volatile sum12 = 0.0f;
	      float volatile sum13 = 0.0f;

	      float volatile sum20 = 0.0f;
	      float volatile sum21 = 0.0f;
	      float volatile sum22 = 0.0f;
	      float volatile sum23 = 0.0f;

	      float volatile sum30 = 0.0f;
	      float volatile sum31 = 0.0f;
	      float volatile sum32 = 0.0f;
	      float volatile sum33 = 0.0f;

	      // Address registers
	      float const *addr_a = &A[i * N/2];
	      float const *addr_b = &B[j/2];
	      float const *end_b  = &B[(N * P + j)/2];
	      float const *addr_c = &C[(i * P + j)/2];

	      int32_t N2 = (int32_t)N * 2;
	      int32_t N3_1 = (-3 * (int32_t)(N/2) + 1) * 4;
	      int32_t P_1  = ((int32_t)(P/2) - 1) * 4;
	      int32_t a0;
	      v2h Vec3;
	      register int32_t k asm("x1") = (int32_t)end_b;

	      //      x12 x14 x13 x15
	      //
	      // x3   x16 x17 x18 x19
	      // x4   x20 x21 x22 x23
	      // x10  x24 x25 x26 x27
	      // x11  x28 x29 x30 x31
	      //
	      //
	      __asm__ volatile(
	          ".balign 16 \n\t"
	          // Create some space on the stack
	          // We push: addr_c
	          "addi sp, sp, -4 \n\t"
	          "sw   %[addr_c], 0(sp) \n\t"
	          // Outer loop: Initialize and preload. Execute this loop P times
	          // "p.lw  x3, %[N2](%[addr_a]!) \n\t"
	          "1: \n\t"
	          "p.lw %[Vec3], 4(%[addr_b]!) \n\t"
	          "p.lw x13, %[P_1](%[addr_b]!) \n\t"
	          "p.lw x14, 4(%[addr_b]!) \n\t"
	          "p.lw x15, %[P_1](%[addr_b]!) \n\t" 

	          "pv.extract.h x3,  %[Vec3], 1;"
            "pv.extract.h x4,  x14, 1;"
            "pv.extract.h %[a0], %[Vec3], 0;"
            "pv.extract.h x11, x14, 0;"
            "pv.pack %[Vec3], x4,  x3;"
            "pv.pack x14, x11, %[a0];"

            "pv.extract.h x3,  x13, 1;"
            "pv.extract.h x4,  x15, 1;"
            "pv.extract.h %[a0], x13, 0;"
            "pv.extract.h x11, x15, 0;"
            "pv.pack x13, x4,  x3;"
            "pv.pack x15, x11, %[a0];"

            "p.lw  x3,  %[N2](%[addr_a]!) \n\t"
            "p.lw  x4,  %[N2](%[addr_a]!) \n\t"
            "p.lw  %[a0], %[N2](%[addr_a]!) \n\t"
            "p.lw  x11, %[N3_1](%[addr_a]!) \n\t"

            "vfdotpex.s.h %[sum00], x3, %[Vec3];"
            "vfdotpex.s.h %[sum01], x3, x14;"
            "vfdotpex.s.h %[sum02], x3, x13;"
            "vfdotpex.s.h %[sum03], x3, x15;"

            "vfdotpex.s.h %[sum10], x4, %[Vec3];"
            "vfdotpex.s.h %[sum11], x4, x14;"
            "vfdotpex.s.h %[sum12], x4, x13;"
            "vfdotpex.s.h %[sum13], x4, x15;"

            "vfdotpex.s.h %[sum20], %[a0], %[Vec3];"
            "vfdotpex.s.h %[sum21], %[a0], x14;"
            "vfdotpex.s.h %[sum22], %[a0], x13;"
            "vfdotpex.s.h %[sum23], %[a0], x15;"

            "vfdotpex.s.h %[sum30], x11, %[Vec3];"
            "vfdotpex.s.h %[sum31], x11, x14;"
            "vfdotpex.s.h %[sum32], x11, x13;"
            "vfdotpex.s.h %[sum33], x11, x15;"

            "bne %[addr_b], x1, 1b \n\t"

            "lw   %[addr_a], 0(sp) \n\t"
	          "addi sp, sp, 4 \n\t"

            "vfcpka.h.s x3, %[sum01], %[sum00];"
            "vfcpka.h.s x4, %[sum03], %[sum02];"
            "p.sw x3, 4(%[addr_a]!) \n\t"
            "p.sw x4, %[P_1](%[addr_a]!) \n\t"

            "vfcpka.h.s x3, %[sum11], %[sum10];"
            "vfcpka.h.s x4, %[sum13], %[sum12];"
            "p.sw x3, 4(%[addr_a]!) \n\t"
            "p.sw x4, %[P_1](%[addr_a]!) \n\t"

            "vfcpka.h.s x3, %[sum21], %[sum20];"
            "vfcpka.h.s x4, %[sum23], %[sum22];"
            "p.sw x3, 4(%[addr_a]!) \n\t"
            "p.sw x4, %[P_1](%[addr_a]!) \n\t"

            "vfcpka.h.s x3, %[sum31], %[sum30];"
            "vfcpka.h.s x4, %[sum33], %[sum32];"
            "p.sw x3, 4(%[addr_a]!) \n\t"
            "p.sw x4, %[P_1](%[addr_a]!) \n\t"
	          : [addr_a] "+&r"(addr_a), [addr_b] "+&r"(addr_b),
	            [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum02] "+&r"(sum02), [sum03] "+&r"(sum03),
	            [sum10] "+&r"(sum10), [sum11] "+&r"(sum11), [sum12] "+&r"(sum12), [sum13] "+&r"(sum13),
	            [sum20] "+&r"(sum20), [sum21] "+&r"(sum21), [sum22] "+&r"(sum22), [sum23] "+&r"(sum23),
	            [sum30] "+&r"(sum30), [sum31] "+&r"(sum31), [sum32] "+&r"(sum32), [sum33] "+&r"(sum33),
	            [Vec3] "+&r"(Vec3),
	            [N3_1] "+r"(N3_1), [P_1] "+r"(P_1), [x1] "+r"(k),
	            [a0] "=r"(a0),
	            [N2] "+r"(N2)
	          : [addr_c] "r"(addr_c) // Inputs
	          : "x3", "x4", "x11", "x13", "x14", "x15", "memory"); // Clobber
	    }
	  }
}



/* 
Desc: MatMul 4x4 Unroll Kernel with asm implementation, optimized for TeraPool architecture
@inp: (float *)  A, B        Pointer to the input matrices
@inp: (float *)  C           Pointer to the output matrix
@inp: (uint32_t) M, N, P     MatMul Dimensions
@inp: (uint32_t) id          Core_id
@inp: (uint32_t) numThreads
@inp: (uint32_t) c_split     Number of cores assigned to every 4 rows in Matrix C  
*/

// Define immediate values that used in asm code.
// #define N3 (matrix_M - 3) * 4
#define _N31 (-3 * (matrix_N/2) + 1) * 4
#define _P1  ((matrix_P/2) - 1) * 4
#define _N2  matrix_N * 2
#define _P2  matrix_P * 2
#define _P21 (-2 * matrix_P + 4)

void matmul_4x4_parallel_f16p_opt_asm(
    float const *__restrict__ A, float const *__restrict__ B,
    float *__restrict__ C, uint32_t M, uint32_t N, uint32_t P, uint32_t id,
    uint32_t numThreads) {

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
  uint32_t group_bank_nums = 1024;              // MemPool = 256
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
  uint32_t k_offset = 2 * (id % c) + (2 * (id / c)) + k_offset_incr; // bowwang: avoiding odd line index
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
  #pragma clang loop unroll(disable)
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
    #pragma clang loop unroll(disable)
    for (uint32_t j = j_offset_counter; j < P_counter; j += 4) {
      // Initialization
      float volatile sum00 = 0.0f;
      float volatile sum01 = 0.0f;
      float volatile sum02 = 0.0f;
      float volatile sum03 = 0.0f;

      float volatile sum10 = 0.0f;
      float volatile sum11 = 0.0f;
      float volatile sum12 = 0.0f;
      float volatile sum13 = 0.0f;

      float volatile sum20 = 0.0f;
      float volatile sum21 = 0.0f;
      float volatile sum22 = 0.0f;
      float volatile sum23 = 0.0f;

      float volatile sum30 = 0.0f;
      float volatile sum31 = 0.0f;
      float volatile sum32 = 0.0f;
      // float volatile sum33 = 0.0f;

      // Address registers
      float const *addr_a_ori = &A[i * N/2];
      float const *addr_b_ori = &B[j/2];
      float const *addr_a = &A[(i * N + k_offset)/2];
      float const *addr_b = &B[(k_offset * P + j)/2];
      float const *end_b  = &B[(N * P + j)/2];
      float const *addr_c = &C[(i * P + j)/2];
      int32_t a0=0;
      v2h Vec3;
      register int32_t k asm("x1") = (int32_t)end_b;

      __asm__ volatile(
          "sw %[addr_c], -4(sp) \n\t"
          :
          : [addr_c] "r"(addr_c)
          :
      );

      __asm__ volatile(
          ".balign 16 \n\t"
          // Outer loop: Initialize and preload. Execute this loop P times
          // TODO arrange
          "add sp, sp, -16 \n\t"
          "sw %[addr_b], 0(sp) \n\t"
          "sw %[addr_a_ori], 4(sp) \n\t"

          "p.lw %[Vec3], 4(%[addr_b]!) \n\t"
          "p.lw x13, %[P_1](%[addr_b]!) \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.lw x15, %[P_1](%[addr_b]!) \n\t" 

          "pv.extract.h x3,  %[Vec3], 1;"
          "pv.extract.h x4,  x14, 1;"
          "pv.extract.h %[a0], %[Vec3], 0;"
          "pv.extract.h x11, x14, 0;"
          "pv.pack %[Vec3], x4,  x3;"
          "pv.pack x14, x11, %[a0];"

          "pv.extract.h x3,  x13, 1;"
          "pv.extract.h x4,  x15, 1;"
          "pv.extract.h %[a0], x13, 0;"
          "pv.extract.h x11, x15, 0;"
          "pv.pack x13, x4,  x3;"
          "pv.pack x15, x11, %[a0];"

          "p.lw  x3,  %[N2](%[addr_a]!) \n\t"
          "p.lw  x4,  %[N2](%[addr_a]!) \n\t"
          "p.lw  %[a0], %[N2](%[addr_a]!) \n\t"
          "p.lw  x11, %[N3_1](%[addr_a]!) \n\t"

          // If reach endpoint, swap address
          "bne %[addr_b], x1, init_comp \n\t"
          "lw x1, 0(sp) \n\t"
          "addi %[addr_a], %[addr_a_ori], 0 \n\t"
          "addi %[addr_b], %[addr_b_ori], 0 \n\t"
          "sw %[addr_b], 0(sp) \n\t"

          // Initial computation + prefetching
          "init_comp: \n\t"
          "vfdotpex.s.h %[sum00], x3, %[Vec3];"
          "vfdotpex.s.h %[sum01], x3, x14;"
          "vfdotpex.s.h %[sum02], x3, x13;"
          "vfdotpex.s.h %[sum03], x3, x15;"

          "vfdotpex.s.h %[sum10], x4, %[Vec3];"
          "vfdotpex.s.h %[sum11], x4, x14;"
          "vfdotpex.s.h %[sum12], x4, x13;"
          "vfdotpex.s.h %[sum13], x4, x15;"

          "vfdotpex.s.h %[sum20], %[a0], %[Vec3];"
          "vfdotpex.s.h %[sum21], %[a0], x14;"
          "vfdotpex.s.h %[sum22], %[a0], x13;"
          "vfdotpex.s.h %[sum23], %[a0], x15;"

          "vfdotpex.s.h %[sum30], x11, %[Vec3];"
          "vfdotpex.s.h %[sum31], x11, x14;"
          "vfdotpex.s.h %[sum32], x11, x13;"
          // "vfdotpex.s.h %[sum33], x11, x15;"
          "xor          %[addr_a_ori], %[addr_a_ori], %[addr_a_ori];"
          "vfdotpex.s.h %[addr_a_ori], x11, x15;"

          "p.lw %[Vec3], 4(%[addr_b]!) \n\t"
          "p.lw x13, %[P_1](%[addr_b]!) \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.lw x15, %[P_1](%[addr_b]!) \n\t" 

          "pv.extract.h x3,  %[Vec3], 1;"
          "pv.extract.h x4,  x14, 1;"
          "pv.extract.h %[a0], %[Vec3], 0;"
          "pv.extract.h x11, x14, 0;"
          "pv.pack %[Vec3], x4,  x3;"
          "pv.pack x14, x11, %[a0];"

          "pv.extract.h x3,  x13, 1;"
          "pv.extract.h x4,  x15, 1;"
          "pv.extract.h %[a0], x13, 0;"
          "pv.extract.h x11, x15, 0;"
          "pv.pack x13, x4,  x3;"
          "pv.pack x15, x11, %[a0];"

          "p.lw  x3,  %[N2](%[addr_a]!) \n\t"
          "p.lw  x4,  %[N2](%[addr_a]!) \n\t"
          "p.lw  %[a0], %[N2](%[addr_a]!) \n\t"
          "p.lw  x11, %[N3_1](%[addr_a]!) \n\t"

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
          "vfdotpex.s.h %[sum00], x3, %[Vec3];"
          "vfdotpex.s.h %[sum01], x3, x14;"
          "vfdotpex.s.h %[sum02], x3, x13;"
          "vfdotpex.s.h %[sum03], x3, x15;"

          "vfdotpex.s.h %[sum10], x4, %[Vec3];"
          "vfdotpex.s.h %[sum11], x4, x14;"
          "vfdotpex.s.h %[sum12], x4, x13;"
          "vfdotpex.s.h %[sum13], x4, x15;"

          "vfdotpex.s.h %[sum20], %[a0], %[Vec3];"
          "vfdotpex.s.h %[sum21], %[a0], x14;"
          "vfdotpex.s.h %[sum22], %[a0], x13;"
          "vfdotpex.s.h %[sum23], %[a0], x15;"

          "vfdotpex.s.h %[sum30], x11, %[Vec3];"
          "vfdotpex.s.h %[sum31], x11, x14;"
          "vfdotpex.s.h %[sum32], x11, x13;"
          "vfdotpex.s.h %[addr_a_ori], x11, x15;"

          "p.lw %[Vec3], 4(%[addr_b]!) \n\t"
          "p.lw x13, %[P_1](%[addr_b]!) \n\t"
          "p.lw x14, 4(%[addr_b]!) \n\t"
          "p.lw x15, %[P_1](%[addr_b]!) \n\t" 

          "pv.extract.h x3,  %[Vec3], 1;"
          "pv.extract.h x4,  x14, 1;"
          "pv.extract.h %[a0], %[Vec3], 0;"
          "pv.extract.h x11, x14, 0;"
          "pv.pack %[Vec3], x4,  x3;"
          "pv.pack x14, x11, %[a0];"

          "pv.extract.h x3,  x13, 1;"
          "pv.extract.h x4,  x15, 1;"
          "pv.extract.h %[a0], x13, 0;"
          "pv.extract.h x11, x15, 0;"
          "pv.pack x13, x4,  x3;"
          "pv.pack x15, x11, %[a0];"

          "p.lw  x3,  %[N2](%[addr_a]!) \n\t"
          "p.lw  x4,  %[N2](%[addr_a]!) \n\t"
          "p.lw  %[a0], %[N2](%[addr_a]!) \n\t"
          "p.lw  x11, %[N3_1](%[addr_a]!) \n\t"

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
          "vfdotpex.s.h %[sum00], x3, %[Vec3];"
          "vfdotpex.s.h %[sum01], x3, x14;"
          "vfdotpex.s.h %[sum02], x3, x13;"
          "vfdotpex.s.h %[sum03], x3, x15;"

          "vfdotpex.s.h %[sum10], x4, %[Vec3];"
          "vfdotpex.s.h %[sum11], x4, x14;"
          "vfdotpex.s.h %[sum12], x4, x13;"
          "vfdotpex.s.h %[sum13], x4, x15;"

          "vfdotpex.s.h %[sum20], %[a0], %[Vec3];"
          "vfdotpex.s.h %[sum21], %[a0], x14;"
          "vfdotpex.s.h %[sum22], %[a0], x13;"
          "vfdotpex.s.h %[sum23], %[a0], x15;"

          "vfdotpex.s.h %[sum30], x11, %[Vec3];"
          "vfdotpex.s.h %[sum31], x11, x14;"
          "vfdotpex.s.h %[sum32], x11, x13;"
          "vfdotpex.s.h %[addr_a_ori], x11, x15;"

          "vfcpka.h.s x3, %[sum01], %[sum00];"
          "vfcpka.h.s x4, %[sum03], %[sum02];"

          "lw %[addr_b_ori], 12(sp) \n\t"
          "p.sw x3, 4(%[addr_b_ori]!) \n\t"
          "p.sw x4, %[P_1](%[addr_b_ori]!) \n\t"

          "vfcpka.h.s x3, %[sum11], %[sum10];"
          "vfcpka.h.s x4, %[sum13], %[sum12];"
          "p.sw x3, 4(%[addr_b_ori]!) \n\t"
          "p.sw x4, %[P_1](%[addr_b_ori]!) \n\t"

          "vfcpka.h.s x3, %[sum21], %[sum20];"
          "vfcpka.h.s x4, %[sum23], %[sum22];"
          "p.sw x3, 4(%[addr_b_ori]!) \n\t"
          "p.sw x4, %[P_1](%[addr_b_ori]!) \n\t"

          "vfcpka.h.s x3, %[sum31], %[sum30];"
          "vfcpka.h.s x4, %[addr_a_ori], %[sum32];"
          "p.sw x3, 4(%[addr_b_ori]!) \n\t"
          "p.sw x4, %[P_1](%[addr_b_ori]!) \n\t"

          "add sp, sp, 16 \n\t"
          : [addr_a] "+&r"(addr_a), [addr_b] "+&r"(addr_b),
            [addr_a_ori] "+&r"(addr_a_ori), [addr_b_ori] "+&r"(addr_b_ori), // Outputs
            [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum02] "+&r"(sum02), [sum03] "+&r"(sum03),
            [sum10] "+&r"(sum10), [sum11] "+&r"(sum11), [sum12] "+&r"(sum12), [sum13] "+&r"(sum13),
            [sum20] "+&r"(sum20), [sum21] "+&r"(sum21), [sum22] "+&r"(sum22), [sum23] "+&r"(sum23),
            [sum30] "+&r"(sum30), [sum31] "+&r"(sum31), [sum32] "+&r"(sum32),
            [Vec3] "+&r"(Vec3), [a0] "=r"(a0), [x1] "+r"(k)
          : [N3_1] "r"(_N31), [P_1] "I"(_P1), [N2] "I"(_N2) // Inputs
          : "x3", "x4", "x11", "x13", "x14", "x15", "memory"); // Clobber
    }
    if (j_offset_counter != c_start) {
      P_counter = j_offset_counter;
      j_offset_counter = c_start;
      goto Mid_loop;
    }
  }
}
