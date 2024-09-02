// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "builtins_v2.h"

#define AXPYF16VEC_UNROLLED4_LOOP                                              \
  {                                                                            \
    a01 = (*(v2h *)&in_a[i]);                                                  \
    a23 = (*(v2h *)&in_a[i + 2]);                                              \
    b01 = (*(v2h *)&in_b[i]);                                                  \
    b23 = (*(v2h *)&in_b[i + 2]);                                              \
    c01 = (*(v2h *)&in_c[i]);                                                  \
    c23 = (*(v2h *)&in_c[i + 2]);                                              \
    asm volatile(                                                              \
        "vfmac.h %[c01], %[a01], %[b01];"                                      \
        "vfmac.h %[c23], %[a23], %[b23];"                                      \
        : [c01] "+&r"(c01), [c23] "+&r"(c23)                                   \
        : [a01] "r"(a01), [a23] "r"(a23), [b01] "r"(b01), [b23] "r"(b23));     \
    (*(v2h *)&in_c[i]) = c01;                                                  \
    (*(v2h *)&in_c[i + 2]) = c23;                                              \
  }

/* Single-core dot-product */
void axpy_f16s(__fp16 *in_a, __fp16 *in_b, __fp16 *in_c, uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    // Kernel execution
    __fp16 *end = in_a + Len / 2;
    do {
      asm volatile("fmadd.h %0, %1, %2, %0;"
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
void axpy_f16s_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *in_c,
                         uint32_t Len) {

  uint32_t core_id = mempool_get_core_id();
  if (core_id == 0) {
    mempool_start_benchmark();
    uint32_t i = 0;
    v2h a01, a23;
    v2h b01, b23;
    v2h c01, c23;
    for (i = 0; i < Len; i += 4) {
      AXPYF16VEC_UNROLLED4_LOOP;
    }
    mempool_stop_benchmark();
  }

  return;
}

/* Parallel dot-product */
void axpy_f16p(__fp16 *in_a, __fp16 *in_b, __fp16 *in_c, uint32_t Len,
               uint32_t nPE) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  __fp16 a, b, c;
  for (uint32_t i = core_id * step; i < core_id * step + step; i++) {
    a = in_a[i];
    b = in_b[i];
    c = in_c[i];
    asm volatile("fmadd.h %0, %1, %2, %0;" : "+&r"(c) : "r"(a), "r"(b));
    in_c[i] = c;
  }
  mempool_barrier(num_cores);

  return;
}

/* Parallel dot-product with loop unrolling*/
void axpy_f16vecp_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *in_c,
                            uint32_t Len, uint32_t nPE) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  uint32_t step = Len / nPE;
  uint32_t i;
  v2h a01, a23;
  v2h b01, b23;
  v2h c01, c23;
  for (i = core_id * step; i < core_id * step + step; i += 4) {
    AXPYF16VEC_UNROLLED4_LOOP;
  }
  mempool_barrier(num_cores);

  return;
}

/* Parallel dot-product with loop unrolling */
/* Load and stores only in local memory */
void axpy_f16vecp_local_unrolled4(__fp16 *in_a, __fp16 *in_b, __fp16 *in_c,
                                  uint32_t Len) {

  uint32_t num_cores = mempool_get_core_count();
  uint32_t core_id = mempool_get_core_id();
  v2h a01, a23;
  v2h b01, b23;
  v2h c01, c23;
  for (uint32_t i = core_id * BANKING_FACTOR; i < Len; i += NUM_BANKS) {
    AXPYF16VEC_UNROLLED4_LOOP;
  }
  mempool_barrier(num_cores);

  return;
}
