// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "runtime.h"
#include "synchronization.h"

volatile float a, b, c;

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    a = 6.3f + (float)core_id;
    b = 7.77f;
    c = a * b;
    //    asm volatile("fmul.s %[c], %[a], %[b];"
    //                 : [c] "=r"(c)
    //                 : [a] "r"(a), [b] "r"(b));
  }
  // wait until all cores have finished
  mempool_barrier(num_cores);
  return 0;
}
