// Copyright 2026 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TensorPool tutorial, part 2: the architecture introduces itself.
//   1. every PE prints its coordinates (PE / tile / group)
//   2. the PEs that drive a tensor engine (TE) print the TE id
//   3. a parallel for-loop is split among the PEs (AXPY) and, at the same
//      time, among the TEs (batched GEMM)

#include <stdbool.h>
#include <stdint.h>

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "baremetal/mempool_redmule_f16.h"

#define LEN 512 // AXPY length (elements)
#define DIM 16  // each TE multiplies one DIM x DIM x DIM matrix product

// L1 arrays. ".l1_prio" places them in the interleaved L1 scratchpad that
// PEs AND tensor engines can access.
int32_t l1_x[LEN] __attribute__((section(".l1_prio")));
int32_t l1_y[LEN] __attribute__((section(".l1_prio")));
// One DIM x DIM matrix per TE for X, W and Y (up to 64 TEs)
__fp16 l1_A[32 * DIM * DIM]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_B[32 * DIM * DIM]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));
__fp16 l1_C[32 * DIM * DIM]
    __attribute__((aligned(sizeof(int32_t)), section(".l1_prio")));

int main() {
  uint32_t pe_id = mempool_get_core_id();
  uint32_t tile_id = mempool_get_tile_id();
  uint32_t subg_id = mempool_get_sg_id();
  uint32_t group_id = mempool_get_group_id();
  uint32_t te_id = mempool_get_redmule_id(); // -1 if this PE drives no TE

  uint32_t num_pes = mempool_get_core_count();
  uint32_t num_tiles = mempool_get_tile_count();
  uint32_t num_subgs = mempool_get_sg_count();
  uint32_t num_groups = mempool_get_group_count();
  uint32_t num_tes = mempool_get_redmule_count();

  mempool_init(pe_id);
  mempool_barrier_init(pe_id);

  /* ---- Part 1: who am I? ------------------------------------------- */
  // All PEs share one UART peripheral, they print one at a time.
  if (pe_id == 0) {
    printf("TensorPool: %u PEs, %u tiles, %u sub-groups, %u groups, %u "
           "tensor-engines\n",
           num_pes, num_tiles, num_subgs, num_groups, num_tes);
  }
  mempool_barrier(num_pes);

  // only the first 8 PEs print
  for (uint32_t turn = 0; turn < 8; turn++) {
    if (pe_id == turn) {
      printf("PE %u: tile %u, sub-group %u, group %u\n", pe_id, tile_id,
             subg_id, group_id);
    }
    mempool_barrier(num_pes);
  }

  /* ---- Part 2: who drives a tensor engine? --------------------------- */
  // In the basic configuration only one PE per sub-group drives a TE.
  for (uint32_t turn = 0; turn < 8; turn++) { // only the first 8 TEs print
    if (te_id == turn) {
      printf("PE %u programs tensor engine %u\n", pe_id, te_id);
    }
    mempool_barrier(num_pes);
  }

  /* ---- Part 3: parallel for-loop on PEs AND engines ---------------- */
  // Initialize with all the PEs (strided loop)
  for (uint32_t i = pe_id; i < LEN; i += num_pes) {
    l1_x[i] = (int32_t)i;
    l1_y[i] = 1;
  }
  for (uint32_t i = pe_id; i < num_tes * DIM * DIM; i += num_pes) {
    l1_A[i] = (__fp16)1.0f; // all ones ...
    l1_B[i] = (__fp16)0.5f; // ... times 0.5: every C element is DIM * 0.5
    l1_C[i] = (__fp16)0.0f;
  }
  mempool_barrier(num_pes);

  mempool_start_benchmark();
  // (a) the TEs start first: the job is asynchronous ...
  if (te_id < num_tes) {
    redmule_start(&l1_A[te_id * DIM * DIM], &l1_B[te_id * DIM * DIM],
                  &l1_C[te_id * DIM * DIM], DIM, DIM, DIM, 0, GEMM);
  }
  // (b) ... meanwhile all the PEs run y = 3 * x + y
  for (uint32_t i = pe_id; i < LEN; i += num_pes) {
    l1_y[i] += 3 * l1_x[i];
  }
  // (c) the PEs driving a TE sleep until the TE raises its end-of-job
  //     event; then everyone synchronizes.
  if (te_id < num_tes) {
    mempool_wfi();
  }
  mempool_barrier(num_pes);
  mempool_stop_benchmark();

  /* ---- Check --------------------------------------------------------- */
  if (pe_id == 0) {
    uint32_t errors = 0;
    for (uint32_t i = 0; i < LEN; i++) {
      errors += (l1_y[i] != (int32_t)(1 + 3 * i));
    }
    for (uint32_t i = 0; i < num_tes * DIM * DIM; i++) {
      errors += ((float)l1_C[i] != (float)DIM * 0.5f);
    }
    printf("Done, %u errors\n", errors);
  }
  mempool_barrier(num_pes);
  return 0;
}
