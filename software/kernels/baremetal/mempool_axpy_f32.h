// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define AXPYF32_UNROLLED4_LOOP                                                 \
  {                                                                            \
    a0 = in_a[i];                                                              \
    b0 = in_b[i];                                                              \
    c0 = in_c[i];                                                              \
    a1 = in_a[i + 1];                                                          \
    b1 = in_b[i + 1];                                                          \
    c1 = in_c[i + 1];                                                          \
    a2 = in_a[i + 2];                                                          \
    b2 = in_b[i + 2];                                                          \
    c2 = in_c[i + 2];                                                          \
    a3 = in_a[i + 3];                                                          \
    b3 = in_b[i + 3];                                                          \
    c3 = in_c[i + 3];                                                          \
    asm volatile(                                                              \
        "fmadd.s %[c0], %[a0], %[b0], %[c0];"                                  \
        "fmadd.s %[c1], %[a1], %[b1], %[c1];"                                  \
        "fmadd.s %[c2], %[a2], %[b2], %[c2];"                                  \
        "fmadd.s %[c3], %[a3], %[b3], %[c3];"                                  \
        : [c0] "+&r"(c0), [c1] "+&r"(c1), [c2] "+&r"(c2), [c3] "+&r"(c3)       \
        : [a0] "r"(a0), [a1] "r"(a1), [a2] "r"(a2), [a3] "r"(a3),              \
          [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3));             \
    in_c[i] = c0;                                                              \
    in_c[i + 1] = c1;                                                          \
    in_c[i + 2] = c2;                                                          \
    in_c[i + 3] = c3;                                                          \
  }

/* Single-core dot-product */
void axpy_f32s(float *in_a, float *in_b, float *in_c, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    float *end = in_a + Len;
    do {
      asm volatile("fmadd.s %0, %1, %2, %0;"
                   : "+&r"(*in_c)
                   : "r"(*in_a), "r"(*in_b));
      in_a++;
      in_b++;
      in_c++;
    } while (in_a < end);
    mempool_stop_benchmark();
  }
  return;
}

/* Single-core dot-product unrolled4 */
void axpy_f32s_unrolled4(float *in_a, float *in_b, float *in_c, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t reminder = Len % 4;
    uint32_t i = 0;

    register float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
    register float b2 = 0.0f, b1 = 0.0f, b0 = 0.0f, b3 = 0.0f;
    register float c2 = 0.0f, c1 = 0.0f, c0 = 0.0f, c3 = 0.0f;

    for (i = 0; i < (Len - reminder); i += 4) {
      AXPYF32_UNROLLED4_LOOP;
    }
    while (i < Len) {
      a0 = in_a[i];
      b0 = in_b[i];
      c0 = in_c[i];
      asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(c0) : "r"(a0), "r"(b0));
      in_c[i] = c0;
      i++;
    }
    mempool_stop_benchmark();
  }
  return;
}

/* Parallel dot-product */
void axpy_f32p(float *in_a, float *in_b, float *in_c, uint32_t Len,
               uint32_t nPE) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;

  register float a, b, c;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    c = in_c[i];
    asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(c) : "r"(a), "r"(b));
    in_c[i] = c;
  }
  mempool_barrier(num_cores);

  return;
}

/* Parallel dot-product with loop unrolling*/
void axpy_f32p_unrolled4(float *in_a, float *in_b, float *in_c, uint32_t Len,
                         uint32_t nPE) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t reminder = step % 4;
  uint32_t i;

  register float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
  register float b2 = 0.0f, b1 = 0.0f, b0 = 0.0f, b3 = 0.0f;
  register float c2 = 0.0f, c1 = 0.0f, c0 = 0.0f, c3 = 0.0f;

  for (i = core_id * step; i < (core_id * step + step) - reminder; i += 4) {
    AXPYF32_UNROLLED4_LOOP;
  }
  i = core_id * step + step - reminder;
  while (i < step) {
    a0 = in_a[i];
    b0 = in_b[i];
    c0 = in_c[i];
    asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(c0) : "r"(a0), "r"(b0));
    in_c[i] = c0;
    i++;
  }
  mempool_barrier(num_cores);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void axpy_f32p_local_unrolled4(float *in_a, float *in_b, float *in_c,
                               uint32_t Len) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  uint32_t const remainder = Len % BANKING_FACTOR;
  uint32_t const idx_stop = Len - remainder;

  register float a0 = 0.0f, a1 = 0.0f, a2 = 0.0f, a3 = 0.0f;
  register float b2 = 0.0f, b1 = 0.0f, b0 = 0.0f, b3 = 0.0f;
  register float c2 = 0.0f, c1 = 0.0f, c0 = 0.0f, c3 = 0.0f;

  for (uint32_t i = core_id * BANKING_FACTOR; i < idx_stop; i += NUM_BANKS) {
    AXPYF32_UNROLLED4_LOOP;
  }
  if (core_id == ((Len % NUM_BANKS) / 4)) {
    for (uint32_t i = Len - remainder; i < Len; i++) {
      a0 = in_a[i];
      b0 = in_b[i];
      asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(c0) : "r"(a0), "r"(b0));
      in_c[i] = c0;
    }
  }
  mempool_barrier(num_cores);

  return;
}
