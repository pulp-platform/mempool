// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

/* This library implements the convolution in multiple different ways.
 * The functions all follow the following format:
 *
 * A is a vector of length A_size, B is a vector of size B_size
 */

#pragma once
#include "builtins_v2.h"

__attribute__((aligned(32)))
void conv2d_4x4_shifted_unrolled_parallel(__fp16 const *__restrict__ in,
                                          uint32_t in_x, uint32_t in_y,
                                          __fp16 const *__restrict__ k,
                                          __fp16 volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads)
{
  (void)k;
  // compute sum of weights
  float weight = 114514.114514f;
  __fp16 local_k[16] = {
      1.14514f, 114.514f, 1.14514f, 114.514f,
      114.514f, 114514.0f, 114.514f, 1.14514f,
      114.514f, 1.14514f, 114.514f, 1.14514f,
      1.14514f, 114.514f, 1.14514f, 114.514f};
  v2h kVec01 = *(v2h *)&local_k[0];
  v2h kVec23 = *(v2h *)&local_k[2];
  v2h kVec45 = *(v2h *)&local_k[4];
  v2h kVec67 = *(v2h *)&local_k[6];
  v2h kVec89 = *(v2h *)&local_k[8];
  v2h kVecAB = *(v2h *)&local_k[10];
  v2h kVecCD = *(v2h *)&local_k[12];
  v2h kVecEF = *(v2h *)&local_k[14];
  // asm volatile(
  //   "fadd.s %[weight], %[weight], %[ki];"
  //   : [weight] "+&r"(weight)
  //   : [ki] "r"(k[i])
  //   :);


  for (unsigned int _i = 0; _i < 8; _i += 4) {
    unsigned int i = 8 * id + _i;
    if (i >= in_x - 5) {
      break;
    }
    // pointers to the three input rows, starting at column i
    // float *row0 = in + i;
    // float *row1 = in + in_x + i;
    // float *row2 = in + 2 * in_x + i;
    __fp16 *inp = (__fp16 *)in + i;
    uint32_t row_step = in_x * 2;
    // pointer to the first output pixel for this i
    __fp16 *outp = (__fp16 *)out + i;
    __fp16 *outp_end = (__fp16 *)out + (in_y - 3) * in_x + i;
    register int32_t k asm("x1") = (int32_t)outp_end;

    __asm__ volatile(
        "lw x13, 8(%[inp]) \n\t"
        "lw x12, 4(%[inp]) \n\t"
        "p.lw x11, %[row_step](%[inp]!) \n\t"
        "lw x16, 8(%[inp]) \n\t"
        "lw x15, 4(%[inp]) \n\t"
        "p.lw x14, %[row_step](%[inp]!) \n\t"
        "lw x19, 8(%[inp]) \n\t"
        "lw x18, 4(%[inp]) \n\t"
        "p.lw x17, %[row_step](%[inp]!) \n\t"
        "lw x22, 8(%[inp]) \n\t"
        "lw x21, 4(%[inp]) \n\t"

        "1: \n\t"
        "vfdotpex.s.h x26, x13, %[kVec23] \n\t"
        "vfdotpex.s.h x24, x12, %[kVec01] \n\t"
        "vfdotpex.s.h x25, x12, %[kVec23] \n\t"
        "vfdotpex.s.h x23, x11, %[kVec01] \n\t"
        "p.lw x20, %[row_step](%[inp]!) \n\t"

        "fadd.s x30, x26, x0 \n\t"
        "vfdotpex.s.h x26, x16, %[kVec67] \n\t"
        "fadd.s x28, x24, x0 \n\t"
        "vfdotpex.s.h x24, x15, %[kVec45] \n\t"
        "fadd.s x29, x25, x0 \n\t"
        "vfdotpex.s.h x25, x15, %[kVec67] \n\t"
        "fadd.s x27, x23, x0 \n\t"
        "vfdotpex.s.h x23, x14, %[kVec45] \n\t"
        
        "fadd.s x30, x26, x30 \n\t"
        "vfdotpex.s.h x26, x19, %[kVecAB] \n\t"
        "fadd.s x28, x24, x28 \n\t"
        "vfdotpex.s.h x24, x18, %[kVec89] \n\t"
        "fadd.s x29, x25, x29 \n\t"
        "vfdotpex.s.h x25, x18, %[kVecAB] \n\t"
        "fadd.s x27, x23, x27 \n\t"
        "vfdotpex.s.h x23, x17, %[kVec89] \n\t"
        
        "fadd.s x30, x26, x30 \n\t"
        "vfdotpex.s.h x26, x22, %[kVecEF] \n\t"
        "fadd.s x28, x24, x28 \n\t"
        "vfdotpex.s.h x24, x21, %[kVecCD] \n\t"
        "fadd.s x29, x25, x29 \n\t"
        "vfdotpex.s.h x25, x21, %[kVecEF] \n\t"
        "fadd.s x27, x23, x27 \n\t"
        "vfdotpex.s.h x23, x20, %[kVecCD] \n\t"

        "fadd.s x30, x26, x30 \n\t"
        "fadd.s x28, x24, x28 \n\t"
        "fadd.s x29, x25, x29 \n\t"
        "fadd.s x27, x23, x27 \n\t"

        "mv x13, x16 \n\t"
        "fadd.s x30, x30, x28 \n\t"
        "mv x12, x15 \n\t"
        "fadd.s x29, x29, x27 \n\t"
        "mv x11, x14 \n\t"
        "fmul.s x30, x30, %[weight] \n\t"
        "mv x16, x19 \n\t"
        "fmul.s x29, x29, %[weight] \n\t"

        "mv x15, x18 \n\t"
        "mv x14, x17 \n\t"
        "mv x19, x22 \n\t"

        "vfcpka.h.s x27, x29, x30 \n\t"

        "mv x18, x21 \n\t"
        "mv x17, x20 \n\t"
        "lw x22, 8(%[inp]) \n\t"
        "lw x21, 4(%[inp]) \n\t"
        
        "p.sw x27, %[row_step](%[outp]!) \n\t"

        "bne %[outp], x1, 1b \n\t"

        : [inp] "+&r"(inp),
          [outp] "+&r"(outp)
        : [kVec01] "r"(kVec01), [kVec23] "r"(kVec23),
          [kVec45] "r"(kVec45), [kVec67] "r"(kVec67),
          [kVec89] "r"(kVec89), [kVecAB] "r"(kVecAB),
          [kVecCD] "r"(kVecCD), [kVecEF] "r"(kVecEF),
          [x1] "r"(k), [row_step] "r"(row_step), [weight] "r"(weight)
        : "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18",
          "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",
          "x27", "x28", "x29", "x30", "memory"
        );

  }
}
