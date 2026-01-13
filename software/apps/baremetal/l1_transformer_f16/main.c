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
#include "l1_transformer_ffn.h"

int main() {

  // Initialization
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_init(core_id);
  mempool_barrier_init(core_id);

  if (core_id == 0) {
    printf("\n\n\n");
    printf("/*********************************************************/\n");
    printf("/** START: Attention Time Domain                        **/\n");
    printf("/*********************************************************/\n");
    printf("\n\n\n");
  }
  mempool_barrier(num_cores);
  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, TBE);

  if (core_id == 0) {
    printf("\n\n\n");
    printf("/*********************************************************/\n");
    printf("/** START: Feed-Forward Neural Network                  **/\n");
    printf("/*********************************************************/\n");
    printf("\n\n\n");
  }
  mempool_barrier(num_cores);
  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  //  if (core_id == 0) {
  //    printf("\n\n\n");
  //    printf("/*********************************************************/\n");
  //    printf("/** START: Attention Embed                              **/\n");
  //    printf("/*********************************************************/\n");
  //    printf("\n\n\n");
  //  }
  //  mempool_barrier(num_cores);
  //  attention(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF, EBT);
  //  if (core_id == 0) {
  //    printf("\n\n\n");
  //    printf("/*********************************************************/\n");
  //    printf("/** START: Feed-Forward Neural Network                  **/\n");
  //    printf("/*********************************************************/\n");
  //    printf("\n\n\n");
  //  }
  //  mempool_barrier(num_cores);
  //  ffn(l2_I, l2_F, l2_b, BEAM, EMBED, TDSAMPLES, CONV1D_WF);

  return 0;
}
