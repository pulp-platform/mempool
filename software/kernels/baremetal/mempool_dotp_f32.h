// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define DOTPF32_UNROLLED4_LOOP                                                 \
  {                                                                            \
    a0 = in_a[i];                                                              \
    a1 = in_a[i + 1];                                                          \
    a2 = in_a[i + 2];                                                          \
    a3 = in_a[i + 3];                                                          \
    b0 = in_b[i];                                                              \
    b1 = in_b[i + 1];                                                          \
    b2 = in_b[i + 2];                                                          \
    b3 = in_b[i + 3];                                                          \
    asm volatile(                                                              \
        "fmadd.s %[local_sum0], %[a0], %[b0], %[local_sum0];"                  \
        "fmadd.s %[local_sum1], %[a1], %[b1], %[local_sum1];"                  \
        "fmadd.s %[local_sum2], %[a2], %[b2], %[local_sum2];"                  \
        "fmadd.s %[local_sum3], %[a3], %[b3], %[local_sum3];"                  \
        : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),      \
          [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)       \
        : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),              \
          [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3));             \
  }

/* Single core reduction */
void mempool_reduction_f32(float *sum, uint32_t num_cores) {

  // The last core to the reduction barrier sums the partial reductions
  if ((num_cores - 1) ==
      __atomic_fetch_add(&red_barrier[0], 1, __ATOMIC_RELAXED)) {

    // Reduction
    uint32_t idx_red = 0;
    float local_sum = 0.0f;
    while (idx_red < NUM_BANKS) {
      asm volatile("fadd.s %0, %0, %1;" : "+&r"(local_sum) : "r"(sum[idx_red]));
      idx_red += BANKING_FACTOR;
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
void mempool_binary_reduction_f32(float *sum, uint32_t core_id,
                                  uint32_t num_cores) {

  uint32_t idx, step = 2, previous_step = 1;
  while (num_cores > 1) {
    idx = (step * (core_id / step)) * BANKING_FACTOR;
    // dump_prova(idx);
    if (__atomic_fetch_add(&red_barrier[idx + previous_step - 1], 1,
                           __ATOMIC_RELAXED)) {

      // Reduction
      float add = sum[idx + previous_step * BANKING_FACTOR];
      asm volatile("fadd.s %0, %0, %1;" : "+&r"(sum[idx]) : "r"(add));

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
void dotp_f32s(float *in_a, float *in_b, float *s, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    float local_sum = 0;
    float *end = in_a + Len;
    do {
      asm volatile("fmadd.s %0, %1, %2, %0;"
                   : "+&r"(local_sum)
                   : "r"(*in_a), "r"(*in_b));
      in_a++;
      in_b++;
    } while (in_a < end);
    *s = local_sum;
    mempool_stop_benchmark();
  }

  return;
}

/* Single-core dot-product unrolled4 */
void dotp_f32s_unrolled4(float *in_a, float *in_b, float *s, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t reminder = Len % 4;
    uint32_t i = 0;

    float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
    float b2 = 0.0f, b1 = 0.0f, b0 = 0.0f, b3 = 0.0f;
    float local_sum0 = 0.0f;
    float local_sum1 = 0.0f;
    float local_sum2 = 0.0f;
    float local_sum3 = 0.0f;
    for (i = 0; i < (Len - reminder); i += 4) {
      DOTPF32_UNROLLED4_LOOP;
    }
    while (i < Len) {
      a0 = in_a[i];
      b0 = in_b[i];
      asm volatile("fmadd.s %0, %1, %2, %0;"
                   : "+&r"(local_sum0)
                   : "r"(a0), "r"(b0));
      i++;
    }
    // Reduction
    asm volatile(
        "fadd.s %[local_sum0], %[local_sum0], %[local_sum1];"
        "fadd.s %[local_sum2], %[local_sum2], %[local_sum3];"
        "fadd.s %[local_sum0], %[local_sum0], %[local_sum2];"
        : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
          [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
        :);
    *s = local_sum0;
    mempool_stop_benchmark();
  }

  return;
}

/* Parallel dot-product */
void dotp_f32p(float *in_a, float *in_b, float *s, uint32_t Len, uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  float local_sum = 0;
  float a, b;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(local_sum) : "r"(a), "r"(b));
  }
  s[core_id * BANKING_FACTOR] = local_sum;

  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f32(s, num_cores);

  return;
}

/* Parallel dot-product with loop unrolling*/
void dotp_f32p_unrolled4(float *in_a, float *in_b, float *s, uint32_t Len,
                         uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t reminder = step % 4;
  uint32_t i;

  float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
  float b2 = 0.0f, b1 = 0.0f, b0 = 0.0f, b3 = 0.0f;
  float local_sum0 = 0.0f;
  float local_sum1 = 0.0f;
  float local_sum2 = 0.0f;
  float local_sum3 = 0.0f;

  for (i = core_id * step; i < (core_id * step + step) - reminder; i += 4) {
    DOTPF32_UNROLLED4_LOOP;
  }
  i = core_id * step + step - reminder;
  while (i < step) {
    a0 = in_a[i];
    b0 = in_b[i];
    asm volatile("fmadd.s %0, %1, %2, %0;"
                 : "+&r"(local_sum0)
                 : "r"(a0), "r"(b0));
    i++;
  }
  asm volatile("fadd.s %[local_sum0], %[local_sum0], %[local_sum1];"
               "fadd.s %[local_sum2], %[local_sum2], %[local_sum3];"
               "fadd.s %[local_sum0], %[local_sum0], %[local_sum2];"
               : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
                 [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
               :);
  s[core_id * BANKING_FACTOR] = local_sum0;
  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f32(s, num_cores);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void dotp_f32p_local_unrolled4(float *in_a, float *in_b, float *s,
                               uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t const remainder = Len % BANKING_FACTOR;
  uint32_t const idx_stop = Len - remainder;

  float a0, a1, a2, a3;
  float b2, b1, b0, b3;
  float local_sum0 = 0.0f;
  float local_sum1 = 0.0f;
  float local_sum2 = 0.0f;
  float local_sum3 = 0.0f;

  for (uint32_t i = core_id * BANKING_FACTOR; i < idx_stop; i += NUM_BANKS) {
    DOTPF32_UNROLLED4_LOOP;
  }
  if (core_id == ((Len % NUM_BANKS) / 4)) {
    for (uint32_t i = idx_stop; i < Len; i++) {
      a0 = in_a[i];
      b0 = in_b[i];
      asm volatile("fmadd.s %0, %1, %2, %0;"
                   : "+&r"(local_sum0)
                   : "r"(a0), "r"(b0));
    }
  }
  asm volatile("fadd.s %[local_sum0], %[local_sum0], %[local_sum1];"
               "fadd.s %[local_sum2], %[local_sum2], %[local_sum3];"
               "fadd.s %[local_sum0], %[local_sum0], %[local_sum2];"
               : [local_sum0] "+&r"(local_sum0), [local_sum1] "+&r"(local_sum1),
                 [local_sum2] "+&r"(local_sum2), [local_sum3] "+&r"(local_sum3)
               :);
  s[core_id * BANKING_FACTOR] = local_sum0;

// The last core to the reduction barrier sums the partial reductions
#if defined(SINGLE_CORE_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  mempool_reduction_f32(s, num_cores);

// A) Cores store locally in sum array
// B) Partial sums are reduced logarithmically
#elif defined(BINARY_REDUCTION)
  uint32_t num_cores = mempool_get_core_count();
  mempool_binary_reduction_f32(s, core_id, num_cores);

#endif

  return;
}
