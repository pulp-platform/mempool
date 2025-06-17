// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

#pragma once
#include "builtins_v2.h"

void gemv_f16vecp_local_unrolled4(__fp16 *in_a, __fp16 *in_x, __fp16 *y,
                                  uint32_t N, uint32_t P) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t const parallel_factor = 32;                  // Number of rows processed in parallel per outer loop
  uint32_t const remainder = N % (2 * BANKING_FACTOR);  // Remaining elements in each row, to be processed in the end with core 0
  uint32_t const idx_stop = N - remainder;

  for (uint32_t i_start = 0; i_start < P; i_start += parallel_factor) {
    uint32_t i = i_start + (core_id % parallel_factor);
    uint32_t valid_parallel_jobs = (P - i_start) < parallel_factor ? (P - i_start) : parallel_factor;   // Number of valid parallel jobs for this iteration
    if (i < P) {
      // For those cores that can be assigned a row
      v2h a01, a23, a45, a67;
      v2h b01, b23, b45, b67;
      float local_sum0 = 0.0f;
      float local_sum1 = 0.0f;
      float local_sum2 = 0.0f;
      float local_sum3 = 0.0f;
      uint32_t j_offset = 2 * (core_id % parallel_factor) * BANKING_FACTOR;   // Reduce bank conflicts
      uint32_t j_block = 2 * parallel_factor * BANKING_FACTOR;                // Number of elements per inner loop
      for (uint32_t j_start = 2 * (core_id / parallel_factor) * parallel_factor * BANKING_FACTOR;
           j_start < idx_stop; j_start += 2 * NUM_BANKS) {
        // Unrolled by 4
        for (uint32_t j_inc = 0; j_inc < j_block; j_inc += 8) {
          uint32_t j = j_start + (j_offset + j_inc) % j_block;
          a01 = (*(v2h *)&in_a[i * N + j]);
          a23 = (*(v2h *)&in_a[i * N + j + 2]);
          a45 = (*(v2h *)&in_a[i * N + j + 4]);
          a67 = (*(v2h *)&in_a[i * N + j + 6]);
          b01 = (*(v2h *)&in_x[j]);
          b23 = (*(v2h *)&in_x[j + 2]);
          b45 = (*(v2h *)&in_x[j + 4]);
          b67 = (*(v2h *)&in_x[j + 6]);
          asm volatile(
            "vfdotpex.s.h %[local_sum0], %[a01], %[b01];"
            "vfdotpex.s.h %[local_sum1], %[a23], %[b23];"
            "vfdotpex.s.h %[local_sum2], %[a45], %[b45];"
            "vfdotpex.s.h %[local_sum3], %[a67], %[b67];"
            : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
              [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
            : [a01] "r"(a01), [a23] "r"(a23), [a45] "r"(a45), [a67] "r"(a67),
              [b01] "r"(b01), [b23] "r"(b23), [b45] "r"(b45), [b67] "r"(b67));
        }
      }
      // Handle the remaining elements with core 0
      if (remainder != 0 && core_id == 0) {
        __fp16 remain_sum = (__fp16)0.0f;
        for (uint32_t j = idx_stop; j < N; j++) {
          __fp16 a0 = in_a[i * N + j];
          __fp16 b0 = in_x[j];
          asm volatile(
            "fmadd.h %[remain_sum], %[a0], %[b0], %[remain_sum];"
            : [remain_sum] "+&r"(remain_sum)
            : [a0] "r"(a0), [b0] "r"(b0));
        }
        float remain_sum_f32;
        asm volatile(
          "fcvt.s.h %[remain_sum_f32], %[remain_sum];"
          "fadd.s %[local_sum0], %[local_sum0], %[remain_sum_f32];"
          : [remain_sum_f32] "=r"(remain_sum_f32),
            [local_sum0] "+&r"(local_sum0)
          : [remain_sum] "r"(remain_sum)
        )
      }
      // Reduction of 4 partial sums
      asm volatile(
        "fadd.s   %[local_sum0], %[local_sum0], %[local_sum1];"
        "fadd.s   %[local_sum2], %[local_sum2], %[local_sum3];"
        "fadd.s   %[local_sum0], %[local_sum0], %[local_sum2];"
        "fcvt.h.s %[local_sum0], %[local_sum0];"
        : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
          [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
        :);
      sum[2 * core_id * BANKING_FACTOR] = *(__fp16 *)&local_sum0;
      uint32_t red_cores = num_cores / parallel_factor;
      uint32_t idx;
      uint32_t step = 2 * parallel_factor;
      uint32_t previous_step = step >> 1;
      while (red_cores > 1) {
        idx = (step * (core_id / step)) * BANKING_FACTOR;
        if (__atomic_fetch_add(&red_barrier[idx + (previous_step - 1) * BANKING_FACTOR + j_offset / 2], 1,
                               __ATOMIC_RELAXED)) {
    
          // Reduction
          __fp16 add = sum[2 * (idx + previous_step * BANKING_FACTOR) + j_offset];
          asm volatile("fadd.h %0, %0, %1;" : "+&r"(sum[2 * idx + j_offset]) : "r"(add));
    
          // Next level of binary tree
          __atomic_store_n(&red_barrier[idx + (previous_step - 1) * BANKING_FACTOR + j_offset / 2], 0,
                           __ATOMIC_RELAXED);
          red_cores = red_cores / 2;
          previous_step = step;
          step = step * 2;
    
        } else {
          // Goes to sleep
          break;
        }
      }
      if (red_cores == 1) {
        // The last core in each row writes the result and accesses the barrier
        y[i] = sum[j_offset];
        mempool_barrier(valid_parallel_jobs);
      }
      else {
        mempool_wfi();
      }
    }
    else {
      // For those cores that cannot be assigned a row
      mempool_wfi();
    }
  }
  return;
}
