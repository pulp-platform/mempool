// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

int32_t mempool_sqrt_q32s(int32_t number, const uint32_t fracBits) {

  int32_t res = 0;
  // register int32_t end = 46341; // smallest integer that is larger than
  // sqrt(0x7FFFFFFF)

  int32_t start = 0;
  int32_t end = 0; // smallest integer that is larger than sqrt(0x7FFFFFFF)
  int32_t a0 = 0, a1 = 0, a2 = 0, a3 = 0;
  asm volatile("li %[a0], 1;"
               "slli  %[a0],%[a0], 9;"
               "slli  %[a1],%[a0], 3;"
               "slli  %[a2],%[a1], 1;"
               "slli  %[a3],%[a2], 2;"
               "add %[end],%[end],%[a0];"
               "add %[end],%[end],%[a1];"
               "add %[end],%[end],%[a2];"
               "add %[end],%[end],%[a3];"
               "addi %[end],%[end],%[imm];"
               : [end] "+&r"(end), [a0] "+&r"(a0), [a1] "+&r"(a1),
                 [a2] "+&r"(a2), [a3] "+&r"(a3)
               : [imm] "I"(773)
               :);
  int32_t mid, mid2;

  //    int32_t m1, m2, tmp, i;
  //    m1 = (end - start) >> 1U;
  //    m2 = m1 * m1;

  if (number > 0) {

    mid = (start + end) >> 1;
    mid2 = mid * mid;
    while (start <= end) {
      if ((mid2 >> fracBits) == number) {
        res = mid;
        break;
      }
      if ((mid2 >> fracBits) < number) {
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

    //        i = 0;
    //        while (i < 5) {
    //            if ((m2 >> fracBits) == number) {
    //                res = m1;
    //                break;
    //            }
    //            if ((m2 >> fracBits) < number) {
    //                m2 = m2 >> 2U;
    //                m1 = m1 >> 1U;
    //            } else {
    //                tmp = (m2 >> 2U);
    //                m2 = (tmp << 3U) + tmp;
    //                m1 = m1 + (m1 >> 1U);
    //            }
    //            i++;
    //        }
  }

  return res;
}
