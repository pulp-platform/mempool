// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#define VERBOSE
#define COMPUTE

#include "l2_data.h"

#include "cnn_state.h"

int main() {
  // Initialization
  uint32_t core_id = mempool_get_core_id();
  mempool_init(core_id);
  mempool_barrier_init(core_id);
  // State update
  cnn_state_update(l1_St1, l1_Wdw, l1_Wpw, NF, NS, D, FK, FD);
  return 0;
}
