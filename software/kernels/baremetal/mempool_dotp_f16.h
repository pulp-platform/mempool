// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

#define DOTPF16VEC_UNROLLED4_LOOP                                              \
  {                                                                            \
    a01 = (*(v2h *)&in_a[i]);                                                  \
    a23 = (*(v2h *)&in_a[i + 2]);                                              \
    b01 = (*(v2h *)&in_b[i]);                                                  \
    b23 = (*(v2h *)&in_b[i + 2]);                                              \
    asm volatile(                                                              \
        "vfdotpex.s.h %[local_sum0], %[a01], %[b01];"                          \
        "vfdotpex.s.h %[local_sum1], %[a23], %[b23];"                          \
        : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1)       \
        : [a01] "r"(a01), [a23] "r"(a23), [b01] "r"(b01), [b23] "r"(b23));     \
  }

/* Single core reduction */
void mempool_reduction_f16(__fp16 *sum, uint32_t num_cores) {

  // The last core to the reduction barrier sums the partial reductions
  if ((num_cores - 1) ==
      __atomic_fetch_add(&red_barrier[0], 1, __ATOMIC_RELAXED)) {

    // Reduction
    uint32_t idx_red = 0;
    __fp16 local_sum = (__fp16)0.0f;
    while (idx_red < NUM_BANKS) {
      asm volatile("fadd.h %0, %0, %1;" : "+&r"(local_sum) : "r"(sum[idx_red]));
      idx_red += 2 * BANKING_FACTOR;
    }
    sum[0] = local_sum;

    __atomic_store_n(&red_barrier[0], 0, __ATOMIC_RELAXED);
    __sync_synchronize();
    wake_up_all();
  }
  mempool_wfi();

  return;
}

/* Bynary tree reduction */
void mempool_binary_reduction_f16(__fp16 *sum, uint32_t core_id,
                                  uint32_t num_cores) {

  uint32_t idx, step = 2, previous_step = 1;
  while (num_cores > 1) {
    idx = (step * (core_id / step)) * BANKING_FACTOR;
    // dump_prova(idx);
    if (__atomic_fetch_add(&red_barrier[idx + previous_step - 1], 1,
                           __ATOMIC_RELAXED)) {

      // Reduction
      __fp16 add = sum[2 * (idx + previous_step * BANKING_FACTOR)];
      asm volatile("fadd.h %0, %0, %1;" : "+&r"(sum[2 * idx]) : "r"(add));

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

/* Single-core dot-product */
void dotp_f16s(__fp16 *in_a, __fp16 *in_b, __fp16 *s, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    __fp16 local_sum = (__fp16)0.0f;
    __fp16 *end = in_a + Len;
    do {
      asm volatile("fmadd.h %0, %1, %2, %0;"
                   : "+&r"(local_sum)
                   : "r"(*in_a), "r"(*in_b));
      in_a++;
      in_b++;
    } while (in_a < end);
    s[0] = local_sum;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  return;
}

/* Single-core dot-product unrolled4 */
void dotp_f16s_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *s, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t i = 0;

    v2h a01, a23;
    v2h b01, b23;
    float local_sum0 = 0.0f;
    float local_sum1 = 0.0f;

    for (i = 0; i < Len; i += 4) {
      DOTPF16VEC_UNROLLED4_LOOP;
    }
    // Reduction
    asm volatile(
        "fadd.s   %[local_sum0], %[local_sum0], %[local_sum1];"
        "fcvt.h.s %[local_sum0], %[local_sum0];"
        : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1)
        :);
    s[0] = *(__fp16 *)&local_sum0;
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  return;
}

/* Parallel dot-product */
void dotp_f16p(__fp16 *in_a, __fp16 *in_b, __fp16 *s, uint32_t Len,
               uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  __fp16 local_sum = (__fp16)0.0f;
  __fp16 a, b;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    asm volatile("fmadd.h %0, %1, %2, %0;" : "+&r"(local_sum) : "r"(a), "r"(b));
  }
  s[2 * core_id * BANKING_FACTOR] = local_sum;

  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f16(s, num_cores);

  return;
}

/* Parallel dot-product with loop unrolling*/
void dotp_f16vecp_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *s, uint32_t Len,
                            uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t i;

  v2h a01, a23;
  v2h b01, b23;
  float local_sum0 = 0.0f;
  float local_sum1 = 0.0f;

  for (i = core_id * step; i < core_id * step + step; i += 4) {
    DOTPF16VEC_UNROLLED4_LOOP;
  }
  asm volatile("fadd.s   %[local_sum0], %[local_sum0], %[local_sum1];"
               "fcvt.h.s %[local_sum0], %[local_sum0];"
               : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1)
               :);
  s[2 * core_id * BANKING_FACTOR] = *(__fp16 *)&local_sum0;
  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f16(s, num_cores);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void dotp_f16vecp_local_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *s,
                                  uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();

  v2h a01, a23;
  v2h b01, b23;
  float local_sum0 = 0.0f;
  float local_sum1 = 0.0f;
  for (uint32_t i = core_id * BANKING_FACTOR; i < Len; i += NUM_BANKS) {
    DOTPF16VEC_UNROLLED4_LOOP;
  }
  asm volatile("fadd.s   %[local_sum0], %[local_sum0], %[local_sum1];"
               "fcvt.h.s %[local_sum0], %[local_sum0];"
               : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1)
               :);
  s[2 * core_id * BANKING_FACTOR] = *(__fp16 *)&local_sum0;

// The last core to the reduction barrier sums the partial reductions
#if defined(SINGLE_CORE_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f16(s, num_cores);
// A) Cores store locally in sum array
// B) Partial sums are reduced logarithmically
#elif defined(BINARY_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  mempool_binary_reduction_f16(s, core_id, num_cores);
#endif

  return;
}
