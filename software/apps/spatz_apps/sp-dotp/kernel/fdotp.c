// Copyright 2022 ETH Zurich and University of Bologna.
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

// Author: Matteo Perotti <mperotti@iis.ee.ethz.ch>

#include "fdotp.h"


// 32-bit dot-product: a * b
float fdotp_v32b(const float *a, const float *b, unsigned int avl) {
  const unsigned int orig_avl = avl;
  unsigned int vl;

  float red;

  // Stripmine and accumulate a partial reduced vector
  do {
    // Set the vl
    asm volatile("vsetvli %0, %1, e32, m8, ta, ma" : "=r"(vl) : "r"(avl));

    // Load chunk a and b
    asm volatile("vle32.v v8,  (%0)" ::"r"(a));
    asm volatile("vle32.v v16, (%0)" ::"r"(b));

    // Multiply and accumulate
    if (avl == orig_avl) {
      asm volatile("vfmul.vv v24, v8, v16");
    } else {
      asm volatile("vfmacc.vv v24, v8, v16");
    }

    // Bump pointers
    a += vl;
    b += vl;
    avl -= vl;
  } while (avl > 0);

  // Reduce and return
  asm volatile("vfredusum.vs v0, v24, v0");
  asm volatile("vfmv.f.s %0, v0" : "=f"(red));
  return red;
}

// 16-bit dot-product: a * b
_Float16 fdotp_v16b(const _Float16 *a, const _Float16 *b, unsigned int avl) {
  const unsigned int orig_avl = avl;
  unsigned int vl;

  _Float16 red;

  // Stripmine and accumulate a partial reduced vector
  do {
    // Set the vl
    asm volatile("vsetvli %0, %1, e16, m8, ta, ma" : "=r"(vl) : "r"(avl));

    // Load chunk a and b
    asm volatile("vle16.v v8,  (%0)" ::"r"(a));
    asm volatile("vle16.v v16, (%0)" ::"r"(b));

    // Multiply and accumulate
    if (avl == orig_avl) {
      asm volatile("vfmul.vv v24, v8, v16");
    } else {
      asm volatile("vfmacc.vv v24, v8, v16");
    }

    // Bump pointers
    a += vl;
    b += vl;
    avl -= vl;
  } while (avl > 0);

  // Reduce and return
  asm volatile("vfredusum.vs v0, v24, v0");
  asm volatile("vfmv.f.s %0, v0" : "=f"(red));
  return red;
}
