// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "omp.h"
#include "printf.h"
#include "runtime.h"

void test(int run) {
#pragma omp parallel for
  for (int i = 0; i < 32; i++) {
    printf("i: %d\n", i);
  }
}

int main() {
  for (int i = 0; i < 10; i++) {
    test(i);
  }
};
