// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

#define AXPYF16VEC_UNROLLED4_LOOP                                              \
  {                                                                            \
    x01 = (*(v2h *)&in_x[i]);                                                  \
    x23 = (*(v2h *)&in_x[i + 2]);                                              \
    x45 = (*(v2h *)&in_x[i + 4]);                                              \
    x67 = (*(v2h *)&in_x[i + 6]);                                              \
    y01 = (*(v2h *)&in_y[i]);                                                  \
    y23 = (*(v2h *)&in_y[i + 2]);                                              \
    y45 = (*(v2h *)&in_y[i + 4]);                                              \
    y67 = (*(v2h *)&in_y[i + 6]);                                              \
    asm volatile("vfmac.h %[y01], %[x01], %[aa];"                              \
                 "vfmac.h %[y23], %[x23], %[aa];"                              \
                 "vfmac.h %[y45], %[x45], %[aa];"                              \
                 "vfmac.h %[y67], %[x67], %[aa];"                              \
                 : [y01] "+&r"(y01), [y23] "+&r"(y23), [y45] "+&r"(y45),       \
                   [y67] "+&r"(y67)                                            \
                 : [x01] "r"(x01), [x23] "r"(x23), [x45] "r"(x45),             \
                   [x67] "r"(x67), [aa] "r"(aa));                              \
    (*(v2h *)&in_y[i]) = y01;                                                  \
    (*(v2h *)&in_y[i + 2]) = y23;                                              \
    (*(v2h *)&in_y[i + 4]) = y45;                                              \
    (*(v2h *)&in_y[i + 6]) = y67;                                              \
  }

/* Single-core dot-product */
void axpy_f16s(uint32_t a, __fp16 *in_x, __fp16 *in_y, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    __fp16 *end = in_x + Len / 2;
    do {
      asm volatile("fmadd.h %0, %1, %2, %0;"
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
void axpy_f16s_unrolled4(uint32_t a, __fp16 *in_x, __fp16 *in_y, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t i = 0;
    uint32_t aa = (a << 16U) | a;
    v2h x01, x23, x45, x67;
    v2h y01, y23, y45, y67;
    for (i = 0; i < Len; i += 8) {
      AXPYF16VEC_UNROLLED4_LOOP;
    }
    mempool_stop_benchmark();
  }

  return;
}

/* Parallel dot-product */
void axpy_f16p(uint32_t a, __fp16 *in_x, __fp16 *in_y, uint32_t Len,
               uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  __fp16 x, y;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    x = in_x[i];
    y = in_y[i];
    asm volatile("fmadd.h %0, %1, %2, %0;" : "+&r"(y) : "r"(a), "r"(x));
    in_y[i] = y;
  }
  mempool_log_barrier(2, core_id);

  return;
}

/* Parallel dot-product with loop unrolling*/
void axpy_f16vecp_unrolled4(uint32_t a, __fp16 *in_x, __fp16 *in_y,
                            uint32_t Len, uint32_t nPE) {

  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t i;

  uint32_t aa = (a << 16U) | a;
  v2h x01, x23, x45, x67;
  v2h y01, y23, y45, y67;
  for (i = core_id * step; i < (core_id * step + step); i += 8) {
    AXPYF16VEC_UNROLLED4_LOOP;
  }
  mempool_log_barrier(2, core_id);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void axpy_f16vecp_local_unrolled4(uint32_t a, __fp16 *in_x, __fp16 *in_y,
                                  uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();

  uint32_t aa = (a << 16U) | a;
  v2h x01, x23, x45, x67;
  v2h y01, y23, y45, y67;
  for (uint32_t i = 2 * core_id * BANKING_FACTOR; i < Len; i += 2 * NUM_BANKS) {
    AXPYF16VEC_UNROLLED4_LOOP;
  }
  mempool_log_barrier(2, core_id);

  return;
}
