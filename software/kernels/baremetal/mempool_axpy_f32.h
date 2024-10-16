// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define AXPYF32_UNROLLED4_LOOP                                                 \
  {                                                                            \
    x0 = in_x[i];                                                              \
    y0 = in_y[i];                                                              \
    x1 = in_x[i + 1];                                                          \
    y1 = in_y[i + 1];                                                          \
    x2 = in_x[i + 2];                                                          \
    y2 = in_y[i + 2];                                                          \
    x3 = in_x[i + 3];                                                          \
    y3 = in_y[i + 3];                                                          \
    asm volatile(                                                              \
        "fmadd.s %[y0], %[a], %[x0], %[y0];"                                   \
        "fmadd.s %[y1], %[a], %[x1], %[y1];"                                   \
        "fmadd.s %[y2], %[a], %[x2], %[y2];"                                   \
        "fmadd.s %[y3], %[a], %[x3], %[y3];"                                   \
        : [y0] "+&r"(y0), [y1] "+&r"(y1), [y2] "+&r"(y2), [y3] "+&r"(y3)       \
        : [x0] "r"(x0), [x1] "r"(x1), [x2] "r"(x2), [x3] "r"(x3), [a] "r"(a)); \
    in_y[i] = y0;                                                              \
    in_y[i + 1] = y1;                                                          \
    in_y[i + 2] = y2;                                                          \
    in_y[i + 3] = y3;                                                          \
  }

/* Single-core dot-product */
void axpy_f32s(float a, float *in_x, float *in_y, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    float *end = in_x + Len;
    do {
      asm volatile("fmadd.s %0, %1, %2, %0;"
                   : "+&r"(*in_y)
                   : "r"(a), "r"(*in_x));
      in_x++;
      in_y++;
    } while (in_x < end);
    mempool_stop_benchmark();
  }
  return;
}

/* Single-core dot-product unrolled4 */
void axpy_f32s_unrolled4(float a, float *in_x, float *in_y, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t reminder = Len % 4;
    uint32_t i = 0;

    register float x2, x1, x0, x3;
    register float y2, y1, y0, y3;
    for (i = 0; i < (Len - reminder); i += 4) {
      AXPYF32_UNROLLED4_LOOP;
    }
    while (i < Len) {
      x0 = in_x[i];
      y0 = in_y[i];
      asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(y0) : "r"(a), "r"(x0));
      in_y[i] = y0;
      i++;
    }
    mempool_stop_benchmark();
  }
  return;
}

/* Parallel dot-product */
void axpy_f32p(float a, float *in_x, float *in_y, uint32_t Len, uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;

  register float x, y;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    x = in_x[i];
    y = in_y[i];
    asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(y) : "r"(a), "r"(x));
    in_y[i] = y;
  }
  mempool_log_barrier(2, core_id);

  return;
}

/* Parallel dot-product with loop unrolling*/
void axpy_f32p_unrolled4(float a, float *in_x, float *in_y, uint32_t Len,
                         uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t reminder = step % 4;
  uint32_t i;

  register float x2, x1, x0, x3;
  register float y2, y1, y0, y3;
  for (i = core_id * step; i < (core_id * step + step) - reminder; i += 4) {
    AXPYF32_UNROLLED4_LOOP;
  }
  i = core_id * step + step - reminder;
  while (i < step) {
    x0 = in_x[i];
    y0 = in_y[i];
    asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(y0) : "r"(a), "r"(x0));
    in_y[i] = y0;
    i++;
  }
  mempool_log_barrier(2, core_id);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void axpy_f32p_local_unrolled4(float a, float *in_x, float *in_y,
                               uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t const remainder = Len % BANKING_FACTOR;
  uint32_t const idx_stop = Len - remainder;

  register float x2, x1, x0, x3;
  register float y2, y1, y0, y3;
  for (uint32_t i = core_id * BANKING_FACTOR; i < idx_stop; i += NUM_BANKS) {
    AXPYF32_UNROLLED4_LOOP;
  }
  if (core_id == ((Len % NUM_BANKS) / 4)) {
    for (uint32_t i = Len - remainder; i < Len; i++) {
      x0 = in_x[i];
      asm volatile("fmadd.s %0, %1, %2, %0;" : "+&r"(y0) : "r"(a), "r"(x0));
      in_y[i] = y0;
    }
  }
  mempool_log_barrier(2, core_id);

  return;
}
