// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

//#define XFP32
//#define XFP16
//#define XFP8
//#define XVFP16
#define SQRT

#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

#if defined(XFP32)
volatile float a, b, c;
#elif defined(XFP16)
volatile __fp16 a, b;
volatile __fp16 c;
#elif defined(XFP8)
volatile __fp16 a, b; // __fp8 not supported, treat as int8
volatile int8_t c;    // __fp8 not supported, treat as int8
#elif defined(XVFP16)
typedef __fp16 v2f16 __attribute__((vector_size(4)));
typedef union {
  float f32;
  v2f16 vec;
} v2h;
volatile float aH, aL, bH, bL;
volatile v2h a, b;
volatile float c;
#elif defined(SQRT)
__fp16 a, c;
#endif

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

#if defined(XFP32)
  if (core_id == 0) {
    a = 6.3f + (float)core_id;
    b = 7.77f;
    asm volatile("fmul.s %[c], %[a], %[b];"
                 : [c] "=r"(c)
                 : [a] "r"(a), [b] "r"(b));
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#elif defined(XFP16)
  if (core_id == 0) {
    a = (__fp16)6.3f + (__fp16)core_id;
    b = (__fp16)7.77f;
    asm volatile("fmul.h %[c], %[a], %[b];"
                 : [c] "=r"(c)
                 : [a] "r"(a), [b] "r"(b));
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#elif defined(XFP8)
  if (core_id == 0) {
    a = (int8_t)6.3f + (int8_t)core_id;
    b = (int8_t)7.77f;
    asm volatile("fmul.b %[c], %[a], %[b];"
                 : [c] "=r"(c)
                 : [a] "r"(a), [b] "r"(b));
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#elif defined(XVFP16)
  if (core_id == 0) {

    aH = 6.35f;
    aL = 7.77f;
    bH = 0.00f;
    bL = 7.77f;
    c = 1.0f;
    asm volatile("vfcpka.h.s %[a], %[aH], %[aL];"
                 "vfcpka.h.s %[b], %[bH], %[bL];"
                 "vfdotpex.s.h %[c], %[a], %[b];"
                 : [c] "=r"(c), [a] "+r"(a), [b] "+r"(b)
                 : [aH] "r"(aH), [bH] "r"(bH), [aL] "r"(aL), [bL] "r"(bL)
                 :);
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#elif defined(SQRT)
  if (core_id == 0) {
    float in = 4.0f;
    asm volatile("fcvt.s.h %[a], %[in];"
                 "fsqrt.h %[c], %[a];"
                 : [c] "=r"(c), [a] "=r"(a)
                 : [in] "r"(in)
                 :);
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#endif

  return 0;
}
