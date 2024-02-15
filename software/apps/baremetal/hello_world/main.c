// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Matheus Cavalcante, ETH Zurich

#include <stdint.h>
#include <string.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t cluster_id = mempool_get_cluster_id();
  uint32_t num_cores = mempool_get_core_count();
  // Initialize synchronization variables
  mempool_barrier_init(core_id);

  if (cluster_id == 0) {
    if (core_id != 0) {
      mempool_wfi();
    }
    printf("Core %3d, Cluster %3d says Hello!\n", core_id, cluster_id);
    wake_up(core_id + 1);
  }
  // wait until all clusters have finished
  mempool_cluster_barrier(num_cores);

  if (cluster_id == 1) {
    if (core_id != 0) {
      mempool_wfi();
    }
    printf("Core %3d, Cluster %3d says Hello!\n", core_id, cluster_id);
    wake_up(core_id + 1);
  }
  // wait until all clusters have finished
  mempool_cluster_barrier(num_cores);

  return 0;
}
