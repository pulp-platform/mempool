// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

inline int32_t mempool_sqrt_q32s(int32_t number, uint32_t fixed_point) {

  int32_t res = 1;
  // register int32_t end = 46341; // smallest integer that is larger than
  // sqrt(0x7FFFFFFF)
  int32_t start = 0;
  int32_t end = 0; // smallest integer that is larger than sqrt(0x7FFFFFFF)
  int32_t a0 = 0;
  asm volatile("li %[a0], 1;"
               "slli  %[a0],%[a0], 9;"
               "add %[end],%[end],%[a0];"
               "slli  %[a0],%[a0], 3;"
               "add %[end],%[end],%[a0];"
               "slli  %[a0],%[a0], 1;"
               "add %[end],%[end],%[a0];"
               "slli  %[a0],%[a0], 2;"
               "add %[end],%[end],%[a0];"
               "addi %[end],%[end],%[imm];"
               : [end] "+&r"(end), [a0] "+&r"(a0)
               : [imm] "I"(773)
               :);
  int32_t mid, mid2;

  if (number > 0) {

    mid = (start + end) >> 1;
    mid2 = mid * mid;
    while (start <= end) {
      asm volatile("srai  %[mid2],%[mid2],%[imm];"
                   : [mid2] "+&r"(mid2)
                   : [imm] "I"(fixed_point)
                   :);
      if (mid2 == number) {
        res = mid;
        break;
      }
      if (mid2 < number) {
        start = mid + 1;
        res = mid;
        mid = (start + end) >> 1;
        mid2 = mid * mid;
      } else {
        end = mid - 1;
        mid = (start + end) >> 1;
        mid2 = mid * mid;
      }
    }
  }

  return res;
}
