// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "omp.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

extern volatile uint32_t tcdm_start_address_reg;
extern volatile uint32_t tcdm_end_address_reg;

int main() {
  uint32_t core_id = mempool_get_core_id();

  if (core_id == 0) {
    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
#pragma omp parallel num_threads(8)
    { printf("%d\n", omp_get_num_threads()); }
    printf("Master Thread: Parallel end\n\n\n");

    printf("Master Thread: Parallel start\n");
    mempool_wait(1000);
#pragma omp parallel
    { printf("%d\n", omp_get_num_threads()); }
    printf("Master Thread: Parallel end\n\n\n");
  }

  return 0;
}
