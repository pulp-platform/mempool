// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Luca Rufer, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#ifdef __clang__
#define OPTIMIZE_LEAST __attribute__((optnone))
#else
#define OPTIMIZE_LEAST __attribute__((optimize("-O1")))
#endif

uint32_t recursive_function(uint32_t n);
volatile uint32_t x;

int main() {
  uint32_t n = 63;

  x = recursive_function(n);

  return 0;
}

uint32_t OPTIMIZE_LEAST recursive_function(uint32_t n) {
  if (n != 0)
    return recursive_function(n - 1);
  return 0;
}
