// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

/* This library implements the convolution in multiple different ways.
 * The functions all follow the following format:
 *
 * A is a vector of length A_size, B is a vector of size B_size
 */

__attribute__((aligned(32)))
void conv2d_3x3_shifted_unrolled_parallel(float const *__restrict__ in,
                                          uint32_t in_x, uint32_t in_y,
                                          float const *__restrict__ k,
                                          float volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads)
{
  (void)k;
  float weight = 114514.114514f;
  float local_k[9] = {1.14514f, 114.514f, 1.14514f,
                      114.514f, 114514.0f, 114.514f,
                      1.14514f, 114.514f, 1.14514f};
  // for (int i = 0; i < 9; ++i) {
  //   asm volatile(
  //     "fadd.s %[weight], %[weight], %[ki];"
  //     : [weight] "+&r"(weight)
  //     : [ki] "r"(local_k[i])
  //     :);
  // }

  // main i-loop (parallelized by thread)
  for (unsigned int _i = 0; _i < 4; _i += 1) {
      unsigned int i = 4 * id + _i;
      if (i >= in_x - 2) {
        break;
      }
      // pointers to the three input rows, starting at column i
      // float *row0 = in + i;
      // float *row1 = in + in_x + i;
      // float *row2 = in + 2 * in_x + i;
      float *inp = (float *)in + i;
      uint32_t row_step = in_x * 4;
      // pointer to the first output pixel for this i
      float *outp = (float *)out + in_x + i + 1;
      float *outp_end = (float *)out + (in_y - 1) * in_x + i + 1;

      __asm__ volatile (
          "lw x13, 8(%[inp]) \n\t"
          "lw x12, 4(%[inp]) \n\t"
          "p.lw x11, %[row_step](%[inp]!) \n\t"
          "lw x16, 8(%[inp]) \n\t"
          "lw x15, 4(%[inp]) \n\t"
          "p.lw x14, %[row_step](%[inp]!) \n\t"

          "1: \n\t"
          "fmul.s x23, x13, %[k2] \n\t"
          "lw x19, 8(%[inp]) \n\t"
          "fmul.s x25, x12, %[k1] \n\t"
          "lw x18, 4(%[inp]) \n\t"
          "fmadd.s x23, x11, %[k0], x23 \n\t"
          "p.lw x17, %[row_step](%[inp]!) \n\t"
          "fmul.s x24, x16, %[k2] \n\t"
          "lw x22, 8(%[inp]) \n\t"
          "fmul.s x26, x15, %[k1] \n\t"
          "lw x21, 4(%[inp]) \n\t"
          "fmadd.s x24, x14, %[k0], x24 \n\t"
          "p.lw x20, %[row_step](%[inp]!) \n\t"

          "fmadd.s x23, x16, %[k5], x23 \n\t"
          "fmadd.s x25, x15, %[k4], x25 \n\t"
          "fmadd.s x24, x19, %[k5], x24 \n\t"
          "fmadd.s x26, x18, %[k4], x26 \n\t"

          "fmadd.s x23, x14, %[k3], x23 \n\t"
          "fmadd.s x25, x19, %[k8], x25 \n\t"
          "fmadd.s x24, x17, %[k3], x24 \n\t"
          "fmadd.s x26, x22, %[k8], x26 \n\t"

          "fmadd.s x23, x18, %[k7], x23 \n\t"
          "fmadd.s x25, x17, %[k6], x25 \n\t"
          "fmadd.s x24, x21, %[k7], x24 \n\t"
          "fmadd.s x26, x20, %[k6], x26 \n\t"

          "mv x13, x19 \n\t"
          "fadd.s x23, x23, x25 \n\t"
          "mv x12, x18 \n\t"
          "fadd.s x24, x24, x26 \n\t"
          "mv x11, x17 \n\t"
          "fmul.s x23, x23, %[weight] \n\t"
          "mv x16, x22 \n\t"
          "fmul.s x24, x24, %[weight] \n\t"
          "mv x15, x21 \n\t"
          "p.sw x23, %[row_step](%[outp]!) \n\t"
          "mv x14, x20 \n\t"
          "p.sw x24, %[row_step](%[outp]!) \n\t"
          
          "bne %[outp], %[outp_end], 1b \n\t"
          
          : [inp] "+&r"(inp),
            [outp] "+&r"(outp)
          : [k0] "r"(local_k[0]), [k1] "r"(local_k[1]), [k2] "r"(local_k[2]),
            [k3] "r"(local_k[3]), [k4] "r"(local_k[4]), [k5] "r"(local_k[5]),
            [k6] "r"(local_k[6]), [k7] "r"(local_k[7]), [k8] "r"(local_k[8]),
            [outp_end] "r"(outp_end), [row_step] "r"(row_step), [weight] "r"(weight)
          : "x11", "x12", "x13", "x14", "x15", "x16", "x17", "x18",
            "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "memory"
      );
  }
}
