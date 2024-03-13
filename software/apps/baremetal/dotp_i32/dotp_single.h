// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* Single-core dot-product */
void dotp_single(int32_t *in_a, int32_t *in_b, int32_t *s, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if (core_id == 0) {

    mempool_start_benchmark();
    // Kernel execution
    register int32_t local_sum = 0;
    int32_t *end = in_a + Len;
    do {
      local_sum += ((*in_a++) * (*in_b++));
    } while (in_a < end);

    *s = local_sum;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
}

/* Single-core dot-product unrolled4 */
void dotp_single_unrolled4(int32_t *in_a, int32_t *in_b, int32_t *s,
                           uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if (core_id == 0) {

    mempool_start_benchmark();
    uint32_t reminder = Len % 4;
    uint32_t i = 0;

    int32_t a0 = 0, b0 = 0, a1 = 0, b1 = 0, a2 = 0, b2 = 0, a3 = 0, b3 = 0;
    register int32_t local_sum_1 = 0;
    register int32_t local_sum_2 = 0;
    register int32_t local_sum_3 = 0;
    register int32_t local_sum_4 = 0;
    for (i = 0; i < (Len - reminder); i += 4) {
      a0 = in_a[i];
      b0 = in_b[i];
      a1 = in_a[i + 1];
      b1 = in_b[i + 1];
      a2 = in_a[i + 2];
      b2 = in_b[i + 2];
      a3 = in_a[i + 3];
      b3 = in_b[i + 3];
      local_sum_1 += a0 * b0;
      local_sum_2 += a1 * b1;
      local_sum_3 += a2 * b2;
      local_sum_4 += a3 * b3;
    }
    while (i < Len) {
      a0 = in_a[i];
      b0 = in_b[i];
      local_sum_1 += a0 * b0;
      i++;
    }
    // Reduction
    local_sum_1 += local_sum_2;
    local_sum_3 += local_sum_4;
    local_sum_1 += local_sum_3;
    *s = local_sum_1;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  // mempool_log_barrier(2, core_id);
}
