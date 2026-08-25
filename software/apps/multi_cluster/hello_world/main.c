// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Matheus Cavalcante, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "mc_printf.h"
#include "mc_runtime.h"

volatile uint32_t turn __attribute__((section(".l1")));

#define CLUSTER_HELLOWORLD(ID)                                                 \
  ({                                                                           \
    if (mc_id == ID) {                                                         \
      while (core_id != turn) {                                                \
        mempool_wfi();                                                         \
      }                                                                        \
      printf("Core[%3d][%3d] says Hello!\n", core_id, mc_id);                  \
      turn++;                                                                  \
      wake_up_all();                                                           \
      while (num_cores != turn) {                                              \
        mempool_wfi();                                                         \
      }                                                                        \
      mc_intra_cluster_sync();                                                 \
    }                                                                          \
    mc_global_barrier_xy();                                                    \
  })

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t mc_id = mc_get_cluster_id();

  mc_barrier_xy_init();

  turn = 0;
  mc_intra_cluster_sync();

  CLUSTER_HELLOWORLD(0);
  CLUSTER_HELLOWORLD(1);
  CLUSTER_HELLOWORLD(2);
  CLUSTER_HELLOWORLD(3);

  return 0;
}
