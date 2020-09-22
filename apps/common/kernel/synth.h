// Copyright 2020 ETH Zurich and University of Bologna.
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

// Author: Samuel Riedel, ETH Zurich

static inline void power_profile(int32_t *const a) {
  // Do this loop M times
  int const num_loops = 2;
  int32_t op_a0 = 88;
  int32_t op_a1 = 4563;
  int32_t op_a2 = -56;
  int32_t op_a3 = 23361;
  int32_t op_a4 = 2;
  int32_t op_a5 = -78967;
  int32_t op_a6 = 2563;
  int32_t op_a7 = -3453;
  int32_t idx = num_loops;
  int32_t im_0 = 0;
  // Temporary registers
  register int32_t op_0;
  register int32_t op_1;
  register int32_t op_2;
  register int32_t op_3;
  register int32_t a0;
  register int32_t a1;
  register int32_t a2;
  register int32_t a3;
  register int32_t a4;
  register int32_t a5;
  register int32_t a6;
  register int32_t a7;
  __asm__ volatile(
      // Outer loop: Calculate four elements of C. Execute this loop P times
      ".balign 16 \n\t"
      "1: \n\t"
      "lw %[a0],  0(%[a]) \n\t"
      "lw %[a1],  4(%[a]) \n\t"
      "lw %[a2],  8(%[a]) \n\t"
      "lw %[a3], 12(%[a]) \n\t"
      "lw %[a4], 16(%[a]) \n\t"
      "lw %[a5], 20(%[a]) \n\t"
      "lw %[a6], 24(%[a]) \n\t"
      "lw %[a7], 28(%[a]) \n\t"
      "lw %[a0], 32(%[a]) \n\t"
      "lw %[a1], 36(%[a]) \n\t"
      "lw %[a2], 40(%[a]) \n\t"
      "lw %[a3], 44(%[a]) \n\t"
      "lw %[a4], 48(%[a]) \n\t"
      "lw %[a5], 52(%[a]) \n\t"
      "lw %[a6], 56(%[a]) \n\t"
      "lw %[a7], 60(%[a]) \n\t"
      "lw %[a0],  0(%[a]) \n\t"
      "lw %[a1],  4(%[a]) \n\t"
      "lw %[a2],  8(%[a]) \n\t"
      "lw %[a3], 12(%[a]) \n\t"
      "lw %[a4], 16(%[a]) \n\t"
      "lw %[a5], 20(%[a]) \n\t"
      "lw %[a6], 24(%[a]) \n\t"
      "lw %[a7], 28(%[a]) \n\t"
      "lw %[a0], 32(%[a]) \n\t"
      "lw %[a1], 36(%[a]) \n\t"
      "lw %[a2], 40(%[a]) \n\t"
      "lw %[a3], 44(%[a]) \n\t"
      "lw %[a4], 48(%[a]) \n\t"
      "lw %[a5], 52(%[a]) \n\t"
      "lw %[a6], 56(%[a]) \n\t"
      "lw %[a7], 60(%[a]) \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 1b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "2: \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "mul %[op_0],%[op_a0],%[op_a4] \n\t"
      "mul %[op_1],%[op_a1],%[op_a5] \n\t"
      "mul %[op_2],%[op_a2],%[op_a6] \n\t"
      "mul %[op_3],%[op_a3],%[op_a7] \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 2b \n\t"
      "addi %[idx], %[idx], %[num_loops] \n\t"
      ".balign 16 \n\t"
      "3: \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "add %[op_0],%[op_a0],%[op_a4] \n\t"
      "add %[op_1],%[op_a1],%[op_a5] \n\t"
      "add %[op_2],%[op_a2],%[op_a6] \n\t"
      "add %[op_3],%[op_a3],%[op_a7] \n\t"
      "addi %[idx], %[idx], -1 \n\t"
      "bne %[idx], %[im_0], 3b \n\t"
      : [ op_0 ] "=&r"(op_0), [ op_1 ] "=&r"(op_1), [ op_2 ] "=&r"(op_2),
        [ op_3 ] "=&r"(op_3), [ a0 ] "=&r"(a0), [ a1 ] "=&r"(a1),
        [ a2 ] "=&r"(a2), [ a3 ] "=&r"(a3), [ a4 ] "=&r"(a4), [ a5 ] "=&r"(a5),
        [ a6 ] "=&r"(a6), [ a7 ] "=&r"(a7), [ idx ] "+&r"(idx)
      : [ im_0 ] "r"(im_0), [ num_loops ] "I"(num_loops), [ op_a0 ] "r"(op_a0),
        [ op_a1 ] "r"(op_a1), [ op_a2 ] "r"(op_a2), [ op_a3 ] "r"(op_a3),
        [ op_a4 ] "r"(op_a4), [ op_a5 ] "r"(op_a5), [ op_a6 ] "r"(op_a6),
        [ op_a7 ] "r"(op_a7), [ a ] "r"(a)
      : "memory");
}
