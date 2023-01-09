// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#define INT32
#define INT16

#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"
dump(x,1);

//volatile float a, b, c;
volatile float16 a, b;
volatile float16 c;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

#if defined(INT32)
  if (core_id == 0) {
    a = 6.3f + (float)core_id;
    b = 7.77f;
    asm volatile("fmul.s %[c], %[a], %[b];"
                 : [c] "=r"(c)
                 : [a] "r"(a), [b] "r"(b));
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#elif defined(INT16)
  if (core_id == 0) {
    a = (float16)6.3f + (float16)core_id;
    b = (float16)7.77f;
    c = a * b;
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
#endif

  return 0;
}
