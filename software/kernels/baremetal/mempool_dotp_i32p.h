// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* Parallel dot-product */
void dotp_i32p(int32_t *in_a, int32_t *in_b, int32_t *s, uint32_t Len,
               uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  register int32_t local_sum = 0;
  register int32_t a, b;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    local_sum += a * b;
  }
  __atomic_fetch_add(&s[0], local_sum, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
  mempool_log_barrier(2, core_id);
#else
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier(num_cores);
#endif
  return;
}

/* Parallel dot-product with loop unrolling*/
void dotp_i32p_unrolled4(int32_t *in_a, int32_t *in_b, int32_t *s, uint32_t Len,
                         uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t reminder = step % 4;
  uint32_t i;

  register int32_t a0 = 0, a1 = 0, a2 = 0, a3 = 0;
  register int32_t b2 = 0, b1 = 0, b0 = 0, b3 = 0;
  register int32_t local_sum0 = 0;
  register int32_t local_sum1 = 0;
  register int32_t local_sum2 = 0;
  register int32_t local_sum3 = 0;
  for (i = core_id * step; i < (core_id * step + step) - reminder; i += 4) {
    a0 = in_a[i];
    b0 = in_b[i];
    a1 = in_a[i + 1];
    b1 = in_b[i + 1];
    a2 = in_a[i + 2];
    b2 = in_b[i + 2];
    a3 = in_a[i + 3];
    b3 = in_b[i + 3];
    local_sum0 += a0 * b0;
    local_sum1 += a1 * b1;
    local_sum2 += a2 * b2;
    local_sum3 += a3 * b3;
  }
  i = core_id * step + step - reminder;
  while (i < step) {
    a0 = in_a[i];
    b0 = in_b[i];
    local_sum0 += a0 * b0;
    i++;
  }
  local_sum0 += local_sum1;
  local_sum2 += local_sum3;
  local_sum0 += local_sum2;
  __atomic_fetch_add(&s[0], local_sum0, __ATOMIC_RELAXED);
#ifdef LOG_BARRIERS
  mempool_log_barrier(2, core_id);
#else
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier(num_cores);
#endif
  return;
}

/* Bynary tree reduction */
void mempool_binary_reduction(int32_t *sum, uint32_t core_id,
                              uint32_t num_cores) {

  uint32_t idx, step = 2, previous_step = 1;
  while (num_cores > 1) {
    idx = (step * (core_id / step)) * BANKING_FACTOR;
    // dump_prova(idx);
    if (__atomic_fetch_add(&red_barrier[idx + previous_step - 1], 1,
                           __ATOMIC_RELAXED)) {

      // Reduction
      sum[idx] += sum[idx + previous_step * BANKING_FACTOR];

      // Next level of binary tree
      __atomic_store_n(&red_barrier[idx + previous_step - 1], 0,
                       __ATOMIC_RELAXED);
      num_cores = num_cores / 2;
      previous_step = step;
      step = step * 2;

    } else {
      // Goes to sleep
      break;
    }
  }

  // Last core wakes everyone
  if (num_cores == 1) {
    __sync_synchronize();
    wake_up_all();
  }
  mempool_wfi();

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
#define NUM_CORES_RED (16)
void dotp_i32p_local_unrolled4(int32_t *in_a, int32_t *in_b, int32_t *s,
                               uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t const remainder = Len % 4;
  uint32_t const idx_stop = Len - remainder;

  register int32_t a0 = 0, a1 = 0, a2 = 0, a3 = 0;
  register int32_t b2 = 0, b1 = 0, b0 = 0, b3 = 0;
  register int32_t local_sum0 = 0;
  register int32_t local_sum1 = 0;
  register int32_t local_sum2 = 0;
  register int32_t local_sum3 = 0;

  for (uint32_t i = core_id * 4; i < idx_stop; i += NUM_BANKS) {
    a0 = in_a[i];
    b0 = in_b[i];
    a1 = in_a[i + 1];
    b1 = in_b[i + 1];
    a2 = in_a[i + 2];
    b2 = in_b[i + 2];
    a3 = in_a[i + 3];
    b3 = in_b[i + 3];
    local_sum0 += a0 * b0;
    local_sum1 += a1 * b1;
    local_sum2 += a2 * b2;
    local_sum3 += a3 * b3;
  }
  if (core_id == ((Len % NUM_BANKS) / 4)) {
    for (uint32_t i = Len - remainder; i < Len; i++) {
      a0 = in_a[i];
      b0 = in_b[i];
      local_sum0 += a0 * b0;
    }
  }
  local_sum0 += local_sum1;
  local_sum2 += local_sum3;
  local_sum0 += local_sum2;

// A) Cores atomically fetch and add in sum variable
// B) A global barrier synchronizes all of them
#if defined(ATOMIC_REDUCTION)
  __atomic_fetch_add(&s[0], local_sum0, __ATOMIC_RELAXED);
  mempool_log_barrier(2, core_id);

// A) Groups of NUM_CORES_RED cores atomically fetch and add in sum array
// B) The last core to the reduction barrier sums the partial reductions
#elif defined(SINGLE_CORE_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  __atomic_fetch_add(
      &s[BANKING_FACTOR * NUM_CORES_RED * (core_id / NUM_CORES_RED)],
      local_sum0, __ATOMIC_RELAXED);
  if ((num_cores - 1) ==
      __atomic_fetch_add(&red_barrier[0], 1, __ATOMIC_RELAXED)) {
    __atomic_store_n(&red_barrier[0], 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    uint32_t idx_red = 0;
    local_sum0 = 0;
    while (idx_red < NUM_BANKS) {
      local_sum0 += s[idx_red];
      idx_red += BANKING_FACTOR * NUM_CORES_RED;
    }
    s[0] = local_sum0;
    wake_up_all();
  }
  mempool_wfi();

// A) Cores store locally in sum array
// B) Partial sums are reduced logarithmically
#elif defined(BINARY_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  s[core_id * 4] = local_sum0;
  mempool_binary_reduction(s, core_id, num_cores);

#endif

  return;
}
