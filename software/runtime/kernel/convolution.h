// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Samuel Riedel, ETH Zurich

/* This library implements the convolution in multiple different ways.
 * The functions all follow the following format:
 *
 * A is a vector of length A_size, B is a vector of size B_size
 */

void conv2d_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                     uint32_t in_y, uint32_t const volatile *__restrict__ k,
                     uint32_t k_x, uint32_t k_y,
                     int32_t volatile *__restrict__ out, uint32_t id,
                     uint32_t numThreads) {
  int boundary_x = (int)(k_x / 2);
  int boundary_y = (int)(k_y / 2);
  // Now we only care about valid entries
  while (id < (unsigned int)boundary_x) {
    id += numThreads;
  }
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Start at the boundary_x
  for (int i = (int)id; i < (int)in_x - boundary_x; i += (int)numThreads) {
    for (int j = boundary_y; j < (int)in_y - boundary_y; j++) {
      sum = 0;
      for (int m = -boundary_y; m < (int)k_y - boundary_y; m++) {
        for (int n = -boundary_x; n < (int)k_x - boundary_x; n++) {
          sum += in[(unsigned int)(j + m) * in_x + (unsigned int)(i + n)] *
                 (int)k[(unsigned int)(m + boundary_y) * k_x +
                        (unsigned int)(n + boundary_x)];
        }
      }
      out[(unsigned int)j * in_x + (unsigned int)i] = sum / (int)weight;
    }
  }
}

void conv2d_shifted_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                             uint32_t in_y, uint32_t const *__restrict__ k,
                             uint32_t k_x, uint32_t k_y,
                             int32_t volatile *__restrict__ out, uint32_t id,
                             uint32_t numThreads) {
  int boundary_x = (int)(k_x / 2);
  int boundary_y = (int)(k_y / 2);
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < k_x * k_y; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (unsigned int i = id; i < in_x - (unsigned int)(2 * boundary_x);
       i += numThreads) {
    for (unsigned int j = 0; j < in_y - (unsigned int)(2 * boundary_y); j++) {
      sum = 0;
      for (unsigned int m = 0; m < k_y; m++) {
        for (unsigned int n = 0; n < k_x; n++) {
          sum += in[(j + m) * in_x + (i + n)] * (int)k[m * k_x + n];
        }
      }
      out[(j + (unsigned int)boundary_y) * in_x +
          (i + (unsigned int)boundary_x)] = sum / (int)weight;
    }
  }
}

void conv2d_3x3_unrolled_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                                  uint32_t in_y, uint32_t const *__restrict__ k,
                                  int32_t volatile *__restrict__ out,
                                  uint32_t id, uint32_t numThreads) {
  int32_t sum;
  uint32_t weight = 0;
  for (unsigned int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  uint32_t div = in_x / numThreads;
  uint32_t rem = in_x % numThreads;
  uint32_t start = div * id;
  uint32_t end = div * (id + 1);
  // Add remainder
  start += id < rem ? id : rem;
  end += id < rem ? id : rem;
  // Now we only care about valid entries
  if (start < 1) {
    start = 1;
  }
  if (end > in_x - 1) {
    end = in_x - 1;
  }

  for (uint32_t i = start; i < end; ++i) {
    for (uint32_t j = 1; j < in_y - 1; j++) {
      sum = 0;
      sum += in[(j - 1) * in_x + (i - 1)] * (int)k[0];
      sum += in[(j - 1) * in_x + (i + 0)] * (int)k[1];
      sum += in[(j - 1) * in_x + (i + 1)] * (int)k[2];
      sum += in[(j + 0) * in_x + (i - 1)] * (int)k[3];
      sum += in[(j + 0) * in_x + (i + 0)] * (int)k[4];
      sum += in[(j + 0) * in_x + (i + 1)] * (int)k[5];
      sum += in[(j + 1) * in_x + (i - 1)] * (int)k[6];
      sum += in[(j + 1) * in_x + (i + 0)] * (int)k[7];
      sum += in[(j + 1) * in_x + (i + 1)] * (int)k[8];
      out[j * in_x + i] = sum / (int)weight;
    }
  }
}

void conv2d_3x3_crazy_parallel(int32_t const *__restrict__ in, uint32_t in_x,
                               uint32_t in_y, int32_t const *__restrict__ k,
                               int32_t volatile *__restrict__ out, uint32_t id,
                               uint32_t numThreads) {
  int32_t weight = 0;
  for (unsigned int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // // TODO implement boundary halo
  // uint32_t div = in_x / numThreads;
  // uint32_t rem = in_x % numThreads;
  // uint32_t start = div * id;
  // uint32_t end = div * (id + 1);
  // // Add remainder
  // start += id < rem ? id : rem;
  // end += id < rem ? id : rem;
  // // Now we only care about valid entries
  // if (start < 1) {
  //   start = 1;
  // }
  // if (end > in_x - 1) {
  //   end = in_x - 1;
  // }

  // TODO implement left and right corner case
if (regular) {
  for (uint32_t c = 4 * id; c < in_x - 6;
       c += 4 * numThreads) { // We compute four output columns per kernel

    // Address registers
    const int32_t *addr_in = (const int32_t *)&in[c];
    const int32_t *addr_out = (const int32_t *)&out[c + 1 + in_x]; // 3x3 Kernel

    // TODO minus phase out 2 rounds
    const int32_t *addr_end = &in[c + in_x * (in_y - 2)];

    const int32_t C_3 = ((int32_t)in_x - 3) * 4;
    const int32_t C_5 = ((int32_t)in_x - 5) * 4;
    const int32_t k0 = k[0];
    const int32_t k1 = k[1];
    const int32_t k2 = k[2];
    const int32_t k3 = k[3];
    const int32_t k4 = k[4];
    const int32_t k5 = k[5];
    const int32_t k6 = k[6];
    const int32_t k7 = k[7];
    const int32_t k8 = k[8];
    const int32_t W = (int32_t)weight;

    // Input
    //  x3  x4  x5  x6  x7  x8
    // Output: TODO Can we make it work with half the outputs?
    //      x9 x10 x11 x12  Top and bottom row in round one, middle in round
    //      two
    //     x13 x14 x15 x16  Middle in round one, top and bottom in round two
    // Kernel:
    //  k0  k1  k2
    //  k3  k4  k5
    //  k6  k7  k8

    // register int32_t k asm("x1") = (int32_t)addr_end;
    __asm__ volatile(
        // Phase in; Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute bottom row
        "mul    x9, %[k0], x3 \n\t"
        "mul   x10, %[k0], x4 \n\t"
        "mul   x11, %[k0], x5 \n\t"
        "mul   x12, %[k0], x6 \n\t"
        "p.mac  x9, %[k1], x4 \n\t"
        "p.mac x10, %[k1], x5 \n\t"
        "p.mac x11, %[k1], x6 \n\t"
        "p.mac x12, %[k1], x7 \n\t"
        "p.mac  x9, %[k2], x5 \n\t"
        "p.mac x10, %[k2], x6 \n\t"
        "p.mac x11, %[k2], x7 \n\t"
        "p.mac x12, %[k2], x8 \n\t"
        // Phase in; Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute middle row
        "p.mac  x9, %[k3], x3 \n\t"
        "p.mac x10, %[k3], x4 \n\t"
        "p.mac x11, %[k3], x5 \n\t"
        "p.mac x12, %[k3], x6 \n\t"
        "p.mac  x9, %[k4], x4 \n\t"
        "p.mac x10, %[k4], x5 \n\t"
        "p.mac x11, %[k4], x6 \n\t"
        "p.mac x12, %[k4], x7 \n\t"
        "p.mac  x9, %[k5], x5 \n\t"
        "p.mac x10, %[k5], x6 \n\t"
        "p.mac x11, %[k5], x7 \n\t"
        "p.mac x12, %[k5], x8 \n\t"
        // Compute bottom row
        "mul   x13, %[k0], x3 \n\t"
        "mul   x14, %[k0], x4 \n\t"
        "mul   x15, %[k0], x5 \n\t"
        "mul   x16, %[k0], x6 \n\t"
        "p.mac x13, %[k1], x4 \n\t"
        "p.mac x14, %[k1], x5 \n\t"
        "p.mac x15, %[k1], x6 \n\t"
        "p.mac x16, %[k1], x7 \n\t"
        "p.mac x13, %[k2], x5 \n\t"
        "p.mac x14, %[k2], x6 \n\t"
        "p.mac x15, %[k2], x7 \n\t"
        "p.mac x16, %[k2], x8 \n\t"

        // Full computation
        "1: \n\t"
        // Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac  x9, %[k6], x3 \n\t"
        "p.mac x10, %[k6], x4 \n\t"
        "p.mac x11, %[k6], x5 \n\t"
        "p.mac x12, %[k6], x6 \n\t"
        "p.mac  x9, %[k7], x4 \n\t"
        "p.mac x10, %[k7], x5 \n\t"
        "p.mac x11, %[k7], x6 \n\t"
        "p.mac x12, %[k7], x7 \n\t"
        "p.mac  x9, %[k8], x5 \n\t"
        "p.mac x10, %[k8], x6 \n\t"
        "p.mac x11, %[k8], x7 \n\t"
        "p.mac x12, %[k8], x8 \n\t"
        // Shift top row
        "div    x9,  x9, %[W] \n\t"
        "div   x10, x10, %[W] \n\t"
        "div   x11, x11, %[W] \n\t"
        "div   x12, x12, %[W] \n\t"
        // Store top row
        "p.sw   x9, 4(%[addr_out]!) \n\t"
        "p.sw  x10, 4(%[addr_out]!) \n\t"
        "p.sw  x11, 4(%[addr_out]!) \n\t"
        "p.sw  x12, %[C_3](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac x13, %[k3], x3 \n\t"
        "p.mac x14, %[k3], x4 \n\t"
        "p.mac x15, %[k3], x5 \n\t"
        "p.mac x16, %[k3], x6 \n\t"
        "p.mac x13, %[k4], x4 \n\t"
        "p.mac x14, %[k4], x5 \n\t"
        "p.mac x15, %[k4], x6 \n\t"
        "p.mac x16, %[k4], x7 \n\t"
        "p.mac x13, %[k5], x5 \n\t"
        "p.mac x14, %[k5], x6 \n\t"
        "p.mac x15, %[k5], x7 \n\t"
        "p.mac x16, %[k5], x8 \n\t"
        // Compute bottom row
        "mul    x9, %[k0], x3 \n\t"
        "mul   x10, %[k0], x4 \n\t"
        "mul   x11, %[k0], x5 \n\t"
        "mul   x12, %[k0], x6 \n\t"
        "p.mac  x9, %[k1], x4 \n\t"
        "p.mac x10, %[k1], x5 \n\t"
        "p.mac x11, %[k1], x6 \n\t"
        "p.mac x12, %[k1], x7 \n\t"
        "p.mac  x9, %[k2], x5 \n\t"
        "p.mac x10, %[k2], x6 \n\t"
        "p.mac x11, %[k2], x7 \n\t"
        "p.mac x12, %[k2], x8 \n\t"
        // Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac x13, %[k6], x3 \n\t"
        "p.mac x14, %[k6], x4 \n\t"
        "p.mac x15, %[k6], x5 \n\t"
        "p.mac x16, %[k6], x6 \n\t"
        "p.mac x13, %[k7], x4 \n\t"
        "p.mac x14, %[k7], x5 \n\t"
        "p.mac x15, %[k7], x6 \n\t"
        "p.mac x16, %[k7], x7 \n\t"
        "p.mac x13, %[k8], x5 \n\t"
        "p.mac x14, %[k8], x6 \n\t"
        "p.mac x15, %[k8], x7 \n\t"
        "p.mac x16, %[k8], x8 \n\t"
        // Shift top row
        "div   x13, x13, %[W] \n\t"
        "div   x14, x14, %[W] \n\t"
        "div   x15, x15, %[W] \n\t"
        "div   x16, x16, %[W] \n\t"
        // Store top row
        "p.sw  x13, 4(%[addr_out]!) \n\t"
        "p.sw  x14, 4(%[addr_out]!) \n\t"
        "p.sw  x15, 4(%[addr_out]!) \n\t"
        "p.sw  x16, %[C_3](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac  x9, %[k3], x3 \n\t"
        "p.mac x10, %[k3], x4 \n\t"
        "p.mac x11, %[k3], x5 \n\t"
        "p.mac x12, %[k3], x6 \n\t"
        "p.mac  x9, %[k4], x4 \n\t"
        "p.mac x10, %[k4], x5 \n\t"
        "p.mac x11, %[k4], x6 \n\t"
        "p.mac x12, %[k4], x7 \n\t"
        "p.mac  x9, %[k5], x5 \n\t"
        "p.mac x10, %[k5], x6 \n\t"
        "p.mac x11, %[k5], x7 \n\t"
        "p.mac x12, %[k5], x8 \n\t"
        // Compute bottom row
        "mul   x13, %[k0], x3 \n\t"
        "mul   x14, %[k0], x4 \n\t"
        "mul   x15, %[k0], x5 \n\t"
        "mul   x16, %[k0], x6 \n\t"
        "p.mac x13, %[k1], x4 \n\t"
        "p.mac x14, %[k1], x5 \n\t"
        "p.mac x15, %[k1], x6 \n\t"
        "p.mac x16, %[k1], x7 \n\t"
        "p.mac x13, %[k2], x5 \n\t"
        "p.mac x14, %[k2], x6 \n\t"
        "p.mac x15, %[k2], x7 \n\t"
        "p.mac x16, %[k2], x8 \n\t"
        // Branch
        "bne %[addr_in], %[addr_end], 1b \n\t"

        // Phase out; Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac  x9, %[k6], x3 \n\t"
        "p.mac x10, %[k6], x4 \n\t"
        "p.mac x11, %[k6], x5 \n\t"
        "p.mac x12, %[k6], x6 \n\t"
        "p.mac  x9, %[k7], x4 \n\t"
        "p.mac x10, %[k7], x5 \n\t"
        "p.mac x11, %[k7], x6 \n\t"
        "p.mac x12, %[k7], x7 \n\t"
        "p.mac  x9, %[k8], x5 \n\t"
        "p.mac x10, %[k8], x6 \n\t"
        "p.mac x11, %[k8], x7 \n\t"
        "p.mac x12, %[k8], x8 \n\t"
        // Shift top row
        "div    x9,  x9, %[W] \n\t"
        "div   x10, x10, %[W] \n\t"
        "div   x11, x11, %[W] \n\t"
        "div   x12, x12, %[W] \n\t"
        // Store top row
        "p.sw   x9, 4(%[addr_out]!) \n\t"
        "p.sw  x10, 4(%[addr_out]!) \n\t"
        "p.sw  x11, 4(%[addr_out]!) \n\t"
        "p.sw  x12, %[C_3](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac x13, %[k3], x3 \n\t"
        "p.mac x14, %[k3], x4 \n\t"
        "p.mac x15, %[k3], x5 \n\t"
        "p.mac x16, %[k3], x6 \n\t"
        "p.mac x13, %[k4], x4 \n\t"
        "p.mac x14, %[k4], x5 \n\t"
        "p.mac x15, %[k4], x6 \n\t"
        "p.mac x16, %[k4], x7 \n\t"
        "p.mac x13, %[k5], x5 \n\t"
        "p.mac x14, %[k5], x6 \n\t"
        "p.mac x15, %[k5], x7 \n\t"
        "p.mac x16, %[k5], x8 \n\t"
        // Phae out; Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, 4(%[addr_in]!) \n\t"
        "p.lw   x8, %[C_5](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac x13, %[k6], x3 \n\t"
        "p.mac x14, %[k6], x4 \n\t"
        "p.mac x15, %[k6], x5 \n\t"
        "p.mac x16, %[k6], x6 \n\t"
        "p.mac x13, %[k7], x4 \n\t"
        "p.mac x14, %[k7], x5 \n\t"
        "p.mac x15, %[k7], x6 \n\t"
        "p.mac x16, %[k7], x7 \n\t"
        "p.mac x13, %[k8], x5 \n\t"
        "p.mac x14, %[k8], x6 \n\t"
        "p.mac x15, %[k8], x7 \n\t"
        "p.mac x16, %[k8], x8 \n\t"
        // Shift top row
        "div   x13, x13, %[W] \n\t"
        "div   x14, x14, %[W] \n\t"
        "div   x15, x15, %[W] \n\t"
        "div   x16, x16, %[W] \n\t"
        // Store top row
        "p.sw  x13, 4(%[addr_out]!) \n\t"
        "p.sw  x14, 4(%[addr_out]!) \n\t"
        "p.sw  x15, 4(%[addr_out]!) \n\t"
        "p.sw  x16, %[C_3](%[addr_out]!) \n\t"
        : [addr_in] "+&r"(addr_in), [addr_out] "+&r"(addr_out) // Outputs
        : [addr_end] "r"(addr_end), [C_3] "r"(C_3), [C_5] "r"(C_5), [W] "r"(W),
          [k0] "r"(k0), [k1] "r"(k1), [k2] "r"(k2), [k3] "r"(k3), [k4] "r"(k4),
          [k5] "r"(k5), [k6] "r"(k6), [k7] "r"(k7),
          [k8] "r"(k8) // Inputs
        : "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
          "x14", "x15", "x16", "memory"); // Clobber
  }
} else {
  for (uint32_t c = 4 * id; c < in_x - 6;
       c += 4 * numThreads) { // We compute four output columns per kernel

    // Address registers
    const int32_t *addr_in = (const int32_t *)&in[c];
    const int32_t *addr_out = (const int32_t *)&out[c + 1 + in_x]; // 3x3 Kernel

    // TODO minus phase out 2 rounds
    const int32_t *addr_end = &in[c + in_x * (in_y - 2)];

    const int32_t C_2 = ((int32_t)in_x - 2) * 4;
    const int32_t C_4 = ((int32_t)in_x - 4) * 4;
    const int32_t k0 = k[0];
    const int32_t k1 = k[1];
    const int32_t k2 = k[2];
    const int32_t k3 = k[3];
    const int32_t k4 = k[4];
    const int32_t k5 = k[5];
    const int32_t k6 = k[6];
    const int32_t k7 = k[7];
    const int32_t k8 = k[8];
    const int32_t W = (int32_t)weight;

    // Input
    //  x3  x4  x5  x6  x7
    // Output: TODO Can we make it work with half the outputs?
    //      x9 x10 x11  Top and bottom in round one, middle in round two
    //     x13 x14 x15  Middle in round one, top and bottom in round two
    // Kernel:
    //  k0  k1  k2
    //  k3  k4  k5
    //  k6  k7  k8

    // register int32_t k asm("x1") = (int32_t)addr_end;
    __asm__ volatile(
        // Phase in; Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4](%[addr_in]!) \n\t"
        // Compute bottom row
        "mul    x9, %[k0], x3 \n\t"
        "mul   x10, %[k0], x4 \n\t"
        "mul   x11, %[k0], x5 \n\t"
        "p.mac  x9, %[k1], x4 \n\t"
        "p.mac x10, %[k1], x5 \n\t"
        "p.mac x11, %[k1], x6 \n\t"
        "p.mac  x9, %[k2], x5 \n\t"
        "p.mac x10, %[k2], x6 \n\t"
        "p.mac x11, %[k2], x7 \n\t"
        // Phase in; Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4][C_4](%[addr_in]!) \n\t"
        "p.mac  x9, %[k3], x3 \n\t"
        "p.mac x10, %[k3], x4 \n\t"
        "p.mac x11, %[k3], x5 \n\t"
        "p.mac  x9, %[k4], x4 \n\t"
        "p.mac x10, %[k4], x5 \n\t"
        "p.mac x11, %[k4], x6 \n\t"
        "p.mac  x9, %[k5], x5 \n\t"
        "p.mac x10, %[k5], x6 \n\t"
        "p.mac x11, %[k5], x7 \n\t"
        // Compute bottom row
        "mul   x13, %[k0], x3 \n\t"
        "mul   x14, %[k0], x4 \n\t"
        "mul   x15, %[k0], x5 \n\t"
        "p.mac x13, %[k1], x4 \n\t"
        "p.mac x14, %[k1], x5 \n\t"
        "p.mac x15, %[k1], x6 \n\t"
        "p.mac x13, %[k2], x5 \n\t"
        "p.mac x14, %[k2], x6 \n\t"
        "p.mac x15, %[k2], x7 \n\t"

        // Full computation
        "1: \n\t"
        // Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac  x9, %[k6], x3 \n\t"
        "p.mac x10, %[k6], x4 \n\t"
        "p.mac x11, %[k6], x5 \n\t"
        "p.mac  x9, %[k7], x4 \n\t"
        "p.mac x10, %[k7], x5 \n\t"
        "p.mac x11, %[k7], x6 \n\t"
        "p.mac  x9, %[k8], x5 \n\t"
        "p.mac x10, %[k8], x6 \n\t"
        "p.mac x11, %[k8], x7 \n\t"
        // Shift top row
        "div    x9,  x9, %[W] \n\t"
        "div   x10, x10, %[W] \n\t"
        "div   x11, x11, %[W] \n\t"
        // Store top row
        "p.sw   x9, 4(%[addr_out]!) \n\t"
        "p.sw  x10, 4(%[addr_out]!) \n\t"
        "p.sw  x11, 4(%[addr_out]!) \n\t"
        "p.sw  x12, %[C_2](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac x13, %[k3], x3 \n\t"
        "p.mac x14, %[k3], x4 \n\t"
        "p.mac x15, %[k3], x5 \n\t"
        "p.mac x16, %[k3], x6 \n\t"
        "p.mac x13, %[k4], x4 \n\t"
        "p.mac x14, %[k4], x5 \n\t"
        "p.mac x15, %[k4], x6 \n\t"
        "p.mac x16, %[k4], x7 \n\t"
        "p.mac x13, %[k5], x5 \n\t"
        "p.mac x14, %[k5], x6 \n\t"
        "p.mac x15, %[k5], x7 \n\t"
        "p.mac x16, %[k5], x8 \n\t"
        // Compute bottom row
        "mul    x9, %[k0], x3 \n\t"
        "mul   x10, %[k0], x4 \n\t"
        "mul   x11, %[k0], x5 \n\t"
        "mul   x12, %[k0], x6 \n\t"
        "p.mac  x9, %[k1], x4 \n\t"
        "p.mac x10, %[k1], x5 \n\t"
        "p.mac x11, %[k1], x6 \n\t"
        "p.mac x12, %[k1], x7 \n\t"
        "p.mac  x9, %[k2], x5 \n\t"
        "p.mac x10, %[k2], x6 \n\t"
        "p.mac x11, %[k2], x7 \n\t"
        "p.mac x12, %[k2], x8 \n\t"
        // Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac x13, %[k6], x3 \n\t"
        "p.mac x14, %[k6], x4 \n\t"
        "p.mac x15, %[k6], x5 \n\t"
        "p.mac x16, %[k6], x6 \n\t"
        "p.mac x13, %[k7], x4 \n\t"
        "p.mac x14, %[k7], x5 \n\t"
        "p.mac x15, %[k7], x6 \n\t"
        "p.mac x16, %[k7], x7 \n\t"
        "p.mac x13, %[k8], x5 \n\t"
        "p.mac x14, %[k8], x6 \n\t"
        "p.mac x15, %[k8], x7 \n\t"
        "p.mac x16, %[k8], x8 \n\t"
        // Shift top row
        "div   x13, x13, %[W] \n\t"
        "div   x14, x14, %[W] \n\t"
        "div   x15, x15, %[W] \n\t"
        "div   x16, x16, %[W] \n\t"
        // Store top row
        "p.sw  x13, 4(%[addr_out]!) \n\t"
        "p.sw  x14, 4(%[addr_out]!) \n\t"
        "p.sw  x15, 4(%[addr_out]!) \n\t"
        "p.sw  x16, %[C_2](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac  x9, %[k3], x3 \n\t"
        "p.mac x10, %[k3], x4 \n\t"
        "p.mac x11, %[k3], x5 \n\t"
        "p.mac x12, %[k3], x6 \n\t"
        "p.mac  x9, %[k4], x4 \n\t"
        "p.mac x10, %[k4], x5 \n\t"
        "p.mac x11, %[k4], x6 \n\t"
        "p.mac x12, %[k4], x7 \n\t"
        "p.mac  x9, %[k5], x5 \n\t"
        "p.mac x10, %[k5], x6 \n\t"
        "p.mac x11, %[k5], x7 \n\t"
        "p.mac x12, %[k5], x8 \n\t"
        // Compute bottom row
        "mul   x13, %[k0], x3 \n\t"
        "mul   x14, %[k0], x4 \n\t"
        "mul   x15, %[k0], x5 \n\t"
        "mul   x16, %[k0], x6 \n\t"
        "p.mac x13, %[k1], x4 \n\t"
        "p.mac x14, %[k1], x5 \n\t"
        "p.mac x15, %[k1], x6 \n\t"
        "p.mac x16, %[k1], x7 \n\t"
        "p.mac x13, %[k2], x5 \n\t"
        "p.mac x14, %[k2], x6 \n\t"
        "p.mac x15, %[k2], x7 \n\t"
        "p.mac x16, %[k2], x8 \n\t"
        // Branch
        "bne %[addr_in], %[addr_end], 1b \n\t"

        // Phase out; Round one
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac  x9, %[k6], x3 \n\t"
        "p.mac x10, %[k6], x4 \n\t"
        "p.mac x11, %[k6], x5 \n\t"
        "p.mac x12, %[k6], x6 \n\t"
        "p.mac  x9, %[k7], x4 \n\t"
        "p.mac x10, %[k7], x5 \n\t"
        "p.mac x11, %[k7], x6 \n\t"
        "p.mac x12, %[k7], x7 \n\t"
        "p.mac  x9, %[k8], x5 \n\t"
        "p.mac x10, %[k8], x6 \n\t"
        "p.mac x11, %[k8], x7 \n\t"
        "p.mac x12, %[k8], x8 \n\t"
        // Shift top row
        "div    x9,  x9, %[W] \n\t"
        "div   x10, x10, %[W] \n\t"
        "div   x11, x11, %[W] \n\t"
        "div   x12, x12, %[W] \n\t"
        // Store top row
        "p.sw   x9, 4(%[addr_out]!) \n\t"
        "p.sw  x10, 4(%[addr_out]!) \n\t"
        "p.sw  x11, 4(%[addr_out]!) \n\t"
        "p.sw  x12, %[C_2](%[addr_out]!) \n\t"
        // Compute middle row
        "p.mac x13, %[k3], x3 \n\t"
        "p.mac x14, %[k3], x4 \n\t"
        "p.mac x15, %[k3], x5 \n\t"
        "p.mac x16, %[k3], x6 \n\t"
        "p.mac x13, %[k4], x4 \n\t"
        "p.mac x14, %[k4], x5 \n\t"
        "p.mac x15, %[k4], x6 \n\t"
        "p.mac x16, %[k4], x7 \n\t"
        "p.mac x13, %[k5], x5 \n\t"
        "p.mac x14, %[k5], x6 \n\t"
        "p.mac x15, %[k5], x7 \n\t"
        "p.mac x16, %[k5], x8 \n\t"
        // Phae out; Round two
        "p.lw   x3, 4(%[addr_in]!) \n\t"
        "p.lw   x4, 4(%[addr_in]!) \n\t"
        "p.lw   x5, 4(%[addr_in]!) \n\t"
        "p.lw   x6, 4(%[addr_in]!) \n\t"
        "p.lw   x7, %[C_4](%[addr_in]!) \n\t"
        // Compute top row
        "p.mac x13, %[k6], x3 \n\t"
        "p.mac x14, %[k6], x4 \n\t"
        "p.mac x15, %[k6], x5 \n\t"
        "p.mac x16, %[k6], x6 \n\t"
        "p.mac x13, %[k7], x4 \n\t"
        "p.mac x14, %[k7], x5 \n\t"
        "p.mac x15, %[k7], x6 \n\t"
        "p.mac x16, %[k7], x7 \n\t"
        "p.mac x13, %[k8], x5 \n\t"
        "p.mac x14, %[k8], x6 \n\t"
        "p.mac x15, %[k8], x7 \n\t"
        "p.mac x16, %[k8], x8 \n\t"
        // Shift top row
        "div   x13, x13, %[W] \n\t"
        "div   x14, x14, %[W] \n\t"
        "div   x15, x15, %[W] \n\t"
        "div   x16, x16, %[W] \n\t"
        // Store top row
        "p.sw  x13, 4(%[addr_out]!) \n\t"
        "p.sw  x14, 4(%[addr_out]!) \n\t"
        "p.sw  x15, 4(%[addr_out]!) \n\t"
        "p.sw  x16, %[C_2](%[addr_out]!) \n\t"
        : [addr_in] "+&r"(addr_in), [addr_out] "+&r"(addr_out) // Outputs
        : [addr_end] "r"(addr_end), [C_2] "r"(C_2), [C_4] "r"(C_4), [W] "r"(W),
          [k0] "r"(k0), [k1] "r"(k1), [k2] "r"(k2), [k3] "r"(k3), [k4] "r"(k4),
          [k5] "r"(k5), [k6] "r"(k6), [k7] "r"(k7),
          [k8] "r"(k8) // Inputs
        : "x3", "x4", "x5", "x6", "x7", "x8", "x9", "x10", "x11", "x12", "x13",
          "x14", "x15", "x16", "memory"); // Clobber
  }
}

void conv2d_3x3_shifted_unrolled_parallel(int32_t const *__restrict__ in,
                                          uint32_t in_x, uint32_t in_y,
                                          uint32_t const *__restrict__ k,
                                          int32_t volatile *__restrict__ out,
                                          uint32_t id, uint32_t numThreads) {
  int32_t sum;
  uint32_t weight = 0;
  for (int i = 0; i < 9; ++i) {
    weight += k[i];
  }
  // TODO implement boundary halo
  // Now we only care about valid entries
  for (unsigned int i = id; i < in_x - 2; i += numThreads) {
    for (unsigned int j = 0; j < in_y - 2; j++) {
      sum = 0;
      sum += in[(j + 0) * in_x + (i + 0)] * (int)k[0];
      sum += in[(j + 0) * in_x + (i + 1)] * (int)k[1];
      sum += in[(j + 0) * in_x + (i + 2)] * (int)k[2];
      sum += in[(j + 1) * in_x + (i + 0)] * (int)k[3];
      sum += in[(j + 1) * in_x + (i + 1)] * (int)k[4];
      sum += in[(j + 1) * in_x + (i + 2)] * (int)k[5];
      sum += in[(j + 2) * in_x + (i + 0)] * (int)k[6];
      sum += in[(j + 2) * in_x + (i + 1)] * (int)k[7];
      sum += in[(j + 2) * in_x + (i + 2)] * (int)k[8];
      out[(j + 1) * in_x + (i + 1)] = sum / (int)weight;
    }
  }
}

// Testing
// Initialize the image in parallel
void init_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                       uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  if (img_y > img_x) {
    for (int i = (int)id; i < (int)img_y; i += (int)numThreads) {
      for (int j = 0; j < (int)img_x; ++j) {
        img[(unsigned int)i * img_x + (unsigned int)j] = (i % 16) + (j % 4);
      }
    }
  } else {
    for (int j = (int)id; j < (int)img_x; j += (int)numThreads) {
      for (int i = 0; i < (int)img_y; ++i) {
        img[(unsigned int)i * img_x + (unsigned int)j] = (i % 16) + (j % 4);
      }
    }
  }
}

// Initialize the image in parallel
void zero_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                       uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  if (img_y > img_x) {
    for (int i = (int)id; i < (int)img_y; i += (int)numThreads) {
      for (int j = 0; j < (int)img_x; ++j) {
        img[(unsigned int)i * img_x + (unsigned int)j] = 0;
      }
    }
  } else {
    for (int j = (int)id; j < (int)img_x; j += (int)numThreads) {
      for (int i = 0; i < (int)img_y; ++i) {
        img[(unsigned int)i * img_x + (unsigned int)j] = 0;
      }
    }
  }
}

extern uint32_t barrier_init;

// Verify and reset the image in parallel
int verify_conv2d_image(volatile int32_t *img, uint32_t img_x, uint32_t img_y,
                        uint32_t id, uint32_t numThreads) {
  // Parallelize over rows
  for (int i = (int)id + 1; i < (int)img_y - 1; i += (int)numThreads) {
    int y = i % 16;
    if (i % 16 == 0)
      y = 4;
    if (i % 16 == 15)
      y = 11;
    for (int j = 1; j < (int)img_x - 1; ++j) {
      int x = ((j % 4) / 2) + 1;
      if ((int)img[i * (int)img_x + j] != x + y) {
        return (i + j) == 0 ? -1 : i * (int)img_x + j;
      }
      img[i * (int)img_x + j] = 0;
    }
  }
  return 0;
}
