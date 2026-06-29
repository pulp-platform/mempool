// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#pragma once

#include "builtins_v2.h"

/* This library implements the GELU activation on a vector of fp16 values.
 * data is an input/output vector of length size.
 * Each element is updated in place with the tanh-based GELU approximation.
 */

void gelu_f16(__fp16 *__restrict__ data, uint32_t size, uint32_t core_id,
              uint32_t numThreads) {

  uint32_t vHalf = 0x38003800;
  uint32_t vCoeffA = 0x29B929B9;
  uint32_t vCoeffB = 0x4EC04EC0;
  uint32_t vCoeffC = 0x48804880;
  uint32_t vSqrt2OverPi = 0x3A623A62;

  uint32_t i, j;
  for (i = 2 * BANKING_FACTOR * core_id; i < size;
       i += 2 * BANKING_FACTOR * numThreads) {
    for (j = 0; j < BANKING_FACTOR / 8; j++) {

      v2h a = *(v2h *)&data[i + j * 8];
      v2h b = *(v2h *)&data[i + j * 8 + 2];
      v2h c = *(v2h *)&data[i + j * 8 + 4];
      v2h d = *(v2h *)&data[i + j * 8 + 6];

      v2h a2, b2, c2, d2;
      v2h a3, b3, c3, d3;
      v2h at, bt, ct, dt;
      v2h at2, bt2, ct2, dt2;
      v2h a_num, b_num, c_num, d_num;
      v2h a_den, b_den, c_den, d_den;
      v2h a_tanh, b_tanh, c_tanh, d_tanh;
      v2h ay, by, cy, dy;

      // a2 = a * a; a3 = a2 * a; same for b, c, d
      asm volatile("vfmul.h %[a2], %[a], %[a];"
                   "vfmul.h %[b2], %[b], %[b];"
                   "vfmul.h %[c2], %[c], %[c];"
                   "vfmul.h %[d2], %[d], %[d];"
                   "vfmul.h %[a3], %[a2], %[a];"
                   "vfmul.h %[b3], %[b2], %[b];"
                   "vfmul.h %[c3], %[c2], %[c];"
                   "vfmul.h %[d3], %[d2], %[d];"
                   : [a2] "=r"(a2), [b2] "=r"(b2), [c2] "=r"(c2), [d2] "=r"(d2),
                     [a3] "=r"(a3), [b3] "=r"(b3), [c3] "=r"(c3), [d3] "=r"(d3)
                   : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d));

      // at = sqrt(2/pi) * (a + 0.044715 * a3); at2 = at * at; same for b, c, d
      at = a;
      bt = b;
      ct = c;
      dt = d;
      asm volatile("vfmac.h %[at],  %[a3],  %[vCoeffA];"
                   "vfmac.h %[bt],  %[b3],  %[vCoeffA];"
                   "vfmac.h %[ct],  %[c3],  %[vCoeffA];"
                   "vfmac.h %[dt],  %[d3],  %[vCoeffA];"
                   "vfmul.h %[at],  %[at],  %[vSqrt2OverPi];"
                   "vfmul.h %[bt],  %[bt],  %[vSqrt2OverPi];"
                   "vfmul.h %[ct],  %[ct],  %[vSqrt2OverPi];"
                   "vfmul.h %[dt],  %[dt],  %[vSqrt2OverPi];"
                   "vfmul.h %[at2], %[at],  %[at];"
                   "vfmul.h %[bt2], %[bt],  %[bt];"
                   "vfmul.h %[ct2], %[ct],  %[ct];"
                   "vfmul.h %[dt2], %[dt],  %[dt];"
                   : [at] "+&r"(at), [bt] "+&r"(bt), [ct] "+&r"(ct),
                     [dt] "+&r"(dt), [at2] "=&r"(at2), [bt2] "=&r"(bt2),
                     [ct2] "=&r"(ct2), [dt2] "=&r"(dt2)
                   : [a3] "r"(a3), [b3] "r"(b3), [c3] "r"(c3), [d3] "r"(d3),
                     [vCoeffA] "r"(vCoeffA), [vSqrt2OverPi] "r"(vSqrt2OverPi));

      // a_num = at * (27 + at2); a_den = 27 + 9 * at2; same for b, c, d
      a_den = *(v2h *)&vCoeffB;
      b_den = *(v2h *)&vCoeffB;
      c_den = *(v2h *)&vCoeffB;
      d_den = *(v2h *)&vCoeffB;
      asm volatile(
          "vfadd.h %[a_num], %[at2], %[vCoeffB];"
          "vfadd.h %[b_num], %[bt2], %[vCoeffB];"
          "vfadd.h %[c_num], %[ct2], %[vCoeffB];"
          "vfadd.h %[d_num], %[dt2], %[vCoeffB];"
          "vfmul.h %[a_num], %[a_num], %[at];"
          "vfmul.h %[b_num], %[b_num], %[bt];"
          "vfmul.h %[c_num], %[c_num], %[ct];"
          "vfmul.h %[d_num], %[d_num], %[dt];"
          "vfmac.h %[a_den], %[at2], %[vCoeffC];"
          "vfmac.h %[b_den], %[bt2], %[vCoeffC];"
          "vfmac.h %[c_den], %[ct2], %[vCoeffC];"
          "vfmac.h %[d_den], %[dt2], %[vCoeffC];"
          : [a_num] "=&r"(a_num), [b_num] "=&r"(b_num), [c_num] "=&r"(c_num),
            [d_num] "=&r"(d_num), [a_den] "+&r"(a_den), [b_den] "+&r"(b_den),
            [c_den] "+&r"(c_den), [d_den] "+&r"(d_den)
          : [at] "r"(at), [bt] "r"(bt), [ct] "r"(ct), [dt] "r"(dt),
            [at2] "r"(at2), [bt2] "r"(bt2), [ct2] "r"(ct2), [dt2] "r"(dt2),
            [vCoeffB] "r"(vCoeffB), [vCoeffC] "r"(vCoeffC));

      // a_tanh = a_num / a_den; ay = 0.5 * a * (1 + a_tanh); same for b, c, d
      asm volatile(
          "vfdiv.h %[a_tanh], %[a_num], %[a_den];"
          "vfdiv.h %[b_tanh], %[b_num], %[b_den];"
          "vfdiv.h %[c_tanh], %[c_num], %[c_den];"
          "vfdiv.h %[d_tanh], %[d_num], %[d_den];"
          "vfmul.h %[ay], %[a], %[vHalf];"
          "vfmul.h %[by], %[b], %[vHalf];"
          "vfmul.h %[cy], %[c], %[vHalf];"
          "vfmul.h %[dy], %[d], %[vHalf];"
          "vfmac.h %[ay], %[ay], %[a_tanh];"
          "vfmac.h %[by], %[by], %[b_tanh];"
          "vfmac.h %[cy], %[cy], %[c_tanh];"
          "vfmac.h %[dy], %[dy], %[d_tanh];"
          : [a_tanh] "=&r"(a_tanh), [b_tanh] "=&r"(b_tanh),
            [c_tanh] "=&r"(c_tanh), [d_tanh] "=&r"(d_tanh), [ay] "=&r"(ay),
            [by] "=&r"(by), [cy] "=&r"(cy), [dy] "=&r"(dy)
          : [a] "r"(a), [b] "r"(b), [c] "r"(c), [d] "r"(d), [a_num] "r"(a_num),
            [b_num] "r"(b_num), [c_num] "r"(c_num), [d_num] "r"(d_num),
            [a_den] "r"(a_den), [b_den] "r"(b_den), [c_den] "r"(c_den),
            [d_den] "r"(d_den), [vHalf] "r"(vHalf));

      *(v2h *)&data[i + j * 8] = ay;
      *(v2h *)&data[i + j * 8 + 2] = by;
      *(v2h *)&data[i + j * 8 + 4] = cy;
      *(v2h *)&data[i + j * 8 + 6] = dy;
    }
  }

  return;
}
