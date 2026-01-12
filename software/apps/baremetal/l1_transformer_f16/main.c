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

#include "l1_transformer_attention.h"

int main() {

  // Initialization
  uint32_t core_id = mempool_get_core_id();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, TBE);

  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, EBT);

  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  return 0;
}
