// Copyright 2025 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Yinrong Li, ETH Zurich

void gemv_f32p_local_unrolled4(float *in_a, float *in_x, float *y, uint32_t N,
                               uint32_t P) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  uint32_t const parallel_factor =
      32; // Number of rows processed in parallel per outer loop
  uint32_t const remainder =
      N % BANKING_FACTOR; // Remaining elements in each row, to be processed in
                          // the end with core 0
  uint32_t const idx_stop = N - remainder;

  for (uint32_t i_start = 0; i_start < P; i_start += parallel_factor) {
    uint32_t i = i_start + (core_id % parallel_factor);
    uint32_t valid_parallel_jobs =
        (P - i_start) < parallel_factor
            ? (P - i_start)
            : parallel_factor; // Number of valid parallel jobs for this
                               // iteration
    if (i < P) {
      // For those cores that can be assigned a row
      float a0, a1, a2, a3;
      float b2, b1, b0, b3;
      float local_sum0 = 0.0f;
      float local_sum1 = 0.0f;
      float local_sum2 = 0.0f;
      float local_sum3 = 0.0f;
      uint32_t j_offset =
          (core_id % parallel_factor) * BANKING_FACTOR; // Reduce bank conflicts
      uint32_t j_block =
          parallel_factor * BANKING_FACTOR; // Number of elements per inner loop
      for (uint32_t j_start =
               (core_id / parallel_factor) * parallel_factor * BANKING_FACTOR;
           j_start < idx_stop; j_start += NUM_BANKS) {
        // Unrolled by 4
        for (uint32_t j_inc = 0; j_inc < j_block; j_inc += 4) {
          uint32_t j = j_start + (j_offset + j_inc) % j_block;
          a0 = in_a[i * N + j];
          a1 = in_a[i * N + j + 1];
          a2 = in_a[i * N + j + 2];
          a3 = in_a[i * N + j + 3];
          b0 = in_x[j];
          b1 = in_x[j + 1];
          b2 = in_x[j + 2];
          b3 = in_x[j + 3];
          asm volatile(
              "fmadd.s %[local_sum0], %[a0], %[b0], %[local_sum0];"
              "fmadd.s %[local_sum1], %[a1], %[b1], %[local_sum1];"
              "fmadd.s %[local_sum2], %[a2], %[b2], %[local_sum2];"
              "fmadd.s %[local_sum3], %[a3], %[b3], %[local_sum3];"
              : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
                [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
              : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),
                [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3));
        }
      }
      // Handle the remaining elements with core 0
      if (remainder != 0 && core_id == 0) {
        for (uint32_t j = idx_stop; j < N; j++) {
          a0 = in_a[i * N + j];
          b0 = in_x[j];
          asm volatile("fmadd.s %[local_sum0], %[a0], %[b0], %[local_sum0];"
                       : [local_sum0] "+&r"(local_sum0)
                       : [a0] "r"(a0), [b0] "r"(b0));
        }
      }
      // Reduction of 4 partial sums
      asm volatile(
          "fadd.s %[local_sum0], %[local_sum0], %[local_sum1];"
          "fadd.s %[local_sum2], %[local_sum2], %[local_sum3];"
          "fadd.s %[local_sum0], %[local_sum0], %[local_sum2];"
          : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
            [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
          :);
      sum[core_id * BANKING_FACTOR] = local_sum0;
      uint32_t red_cores = num_cores / parallel_factor;
      uint32_t idx;
      uint32_t step = 2 * parallel_factor;
      uint32_t previous_step = step >> 1;
      while (red_cores > 1) {
        idx = (step * (core_id / step)) * BANKING_FACTOR;
        if (__atomic_fetch_add(
                &red_barrier[idx + (previous_step - 1) * BANKING_FACTOR +
                             j_offset],
                1, __ATOMIC_RELAXED)) {

          // Reduction
          float add = sum[idx + previous_step * BANKING_FACTOR + j_offset];
          asm volatile("fadd.s %0, %0, %1;"
                       : "+&r"(sum[idx + j_offset])
                       : "r"(add));

          // Next level of binary tree
          __atomic_store_n(
              &red_barrier[idx + (previous_step - 1) * BANKING_FACTOR +
                           j_offset],
              0, __ATOMIC_RELAXED);
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
      } else {
        mempool_wfi();
      }
    } else {
      // For those cores that cannot be assigned a row
      mempool_wfi();
    }
  }
  return;
}
