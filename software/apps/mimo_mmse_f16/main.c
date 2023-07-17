// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

typedef signed short v2s __attribute__((vector_size(4)));
typedef __fp16 v2f16 __attribute__((vector_size(4)));
typedef union {
    float f32;
    v2f16 vec;
} v2h;

#include "mimo_mmse_f16s.h"

/* DATA */
#include "data_mimo_mmse_f16.h"

//#define SINGLE
#define PARALLEL
//#define FOLDED

#ifdef SINGLE
__fp16 ch_matrix[2 * N_TX * N_RX]    __attribute__((section(".l1")));
__fp16 in_matrix[2 * N_TX * N_TX]    __attribute__((section(".l1")));
__fp16 out_matrix[2 * N_TX * N_TX]   __attribute__((section(".l1")));
__fp16 sigma[2 * N_TX]  __attribute__((section(".l1")));
__fp16 b[2 * N_RX]      __attribute__((section(".l1")));

__fp16 s[2 * N_TX]   __attribute__((section(".l1")));
__fp16 x[2 * N_TX]   __attribute__((section(".l1")));
__fp16 y[2 * N_TX]   __attribute__((section(".l1")));
#endif

#ifdef PARALLEL
__fp16 in_matrix[2 * N_TX * N_TX * N_ITR]    __attribute__((section(".l1_prio"), aligned(N_BANKS)));
__fp16 out_matrix[2 * N_TX * N_TX * N_ITR]   __attribute__((section(".l1_prio"), aligned(N_BANKS)));
__fp16 s[2 * N_TX * N_ITR]   __attribute__((section(".l1_prio"), aligned(N_BANKS)));
__fp16 x[2 * N_TX * N_ITR]   __attribute__((section(".l1_prio"), aligned(N_BANKS)));
__fp16 y[2 * N_TX * N_ITR]   __attribute__((section(".l1_prio"), aligned(N_BANKS)));

__fp16 ch_matrix[2 * N_TX * N_RX * N_ITR]    __attribute__((section(".l1_prio")));
__fp16 b[2 * N_RX * N_ITR]        __attribute__((section(".l1_prio")));
__fp16 sigma[2 * N_TX * N_ITR]    __attribute__((section(".l1_prio")));
#endif

void initialize(__fp16 *matrix, __fp16 *data, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i += num_cores) {
    matrix[i] = data[i];
  }
  mempool_barrier(num_cores);
  return;
}

void initialize_zeros(__fp16 *matrix, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  __fp16 zero = (__fp16) (0x0000);
  for (i = core_id; i < 2 * dim; i += num_cores) {
    matrix[i] = zero;
  }
  mempool_barrier(num_cores);
  return;
}

void verify_result(__fp16 *pRes, __fp16 *pExp, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {
      __fp16 error;
      __fp16 exp = pExp[i];
      __fp16 res = pRes[i];
      asm volatile(
        "fsub.h %[error], %[res], %[exp];"
        : [error] "=&r"(error)
        : [res] "r"(res), [exp] "r"(exp)
        : );
      if (*(int32_t*)&error != 0) {
        printf("(%d): 0x%08x - 0x%08x - 0x%08x\n", i / 2, *(int32_t*)&error, *(int32_t*)&exp, *(int32_t*)&res);
      }
    }
  }
}

void write_result(__fp16 *pRes, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {

      __fp16 in = pRes[i];
//      uint32_t out = "0xFFFF0000" || *(uint32_t*)&in;
      float cvt_out;
      asm volatile(
        "fcvt.h.s %[cvt_out], %[in];"
        : [cvt_out] "=&r"(cvt_out)
        : [in] "r" (in)
        : );

    }
  }
}

// Driver program
void single_core_mimo_mmse() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX*N_TX, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX*N_TX, core_id, num_cores);
  initialize_zeros(out_matrix, N_TX*N_TX, core_id, num_cores);
  /* Initialize vectors */
  initialize(sigma, In_sigma, N_TX, core_id, num_cores);
  initialize(b, In_b, N_RX, core_id, num_cores);
  /* Initialize results */
  initialize_zeros(s, N_TX, core_id, num_cores);
  initialize_zeros(y, N_TX, core_id, num_cores);
  initialize_zeros(x, N_TX, core_id, num_cores);

  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f16s(ch_matrix, in_matrix, sigma, N_RX, N_TX, 0);
    mempool_MVP_conjtransp_f16s(ch_matrix, b, s, N_RX, N_TX, 0);
    mempool_cholesky_f16s(in_matrix, out_matrix, N_TX);
    mempool_Ltrisol_f16s(out_matrix, s, y, N_TX);
    mempool_Lttrisol_f16s(out_matrix, y, x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  verify_result(x, Out_x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}

// Driver program
void parallel_mimo_mmse_cholesky() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX*N_TX*N_ITR, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX*N_TX*N_ITR, core_id, num_cores);
  initialize_zeros(out_matrix, N_TX*N_TX*N_ITR, core_id, num_cores);
  /* Initialize vectors */
  uint32_t i = 0;
  for (i = core_id; i < (N_TX*N_ITR); i += num_cores) {
    sigma[2 * i] = In_sigma[i];
  }
  mempool_barrier(num_cores);
  initialize(b, In_b, N_RX*N_ITR, core_id, num_cores);
  /* Initialize results */
  initialize_zeros(s, N_TX*N_ITR, core_id, num_cores);
  initialize_zeros(y, N_TX*N_ITR, core_id, num_cores);
  initialize_zeros(x, N_TX*N_ITR, core_id, num_cores);
  dump_res1(core_id);

  /* Benchmark */
#ifdef FOLDED
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    __fp16* ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    __fp16* sigma_ptr = sigma + itr * (2 * N_TX);
    __fp16* b_ptr = b + itr * (2 * N_RX);

    __fp16* in_matrix_ptr = in_matrix + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_TX * N_BANKS);
    __fp16* out_matrix_ptr = out_matrix + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_TX * N_BANKS);
    __fp16* s_ptr = s + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_BANKS);
    __fp16* y_ptr = y + (itr % num_cores) * (2 * N_TX) + (itr / num_cores) * (N_BANKS);
    __fp16* x_ptr = x + itr * (2 * N_TX);

    mempool_hermitian_f16s(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX, N_TX, 1);
    mempool_MVP_conjtransp_f16s(ch_matrix_ptr, b_ptr, s_ptr, N_RX, N_TX, 1);
    mempool_cholesky_folded_f16s(in_matrix_ptr, out_matrix_ptr, N_TX);
    mempool_Ltrisol_folded_f16s(out_matrix_ptr, s_ptr, y_ptr, N_TX);
    mempool_Lttrisol_folded_f16s(out_matrix_ptr, y_ptr, x_ptr, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#else
  // Each iteration is assigned to a processor
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {

    __fp16* ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    __fp16* sigma_ptr = sigma + itr * (2 * N_TX);
    __fp16* b_ptr = b + itr * (2 * N_RX);

    __fp16* in_matrix_ptr = in_matrix + itr * (2 * N_TX * N_TX);
    __fp16* out_matrix_ptr = out_matrix + itr * (2 * N_TX * N_TX);
    __fp16* s_ptr = s + itr * (2 * N_TX);
    __fp16* y_ptr = y + itr * (2 * N_TX);
    __fp16* x_ptr = x + itr * (2 * N_TX);

    mempool_hermitian_f16s(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX, N_TX, 0);
    mempool_MVP_conjtransp_f16s(ch_matrix_ptr, b_ptr, s_ptr, N_RX, N_TX, 0);
    mempool_cholesky_f16s(in_matrix_ptr, out_matrix_ptr, N_TX);
    mempool_Ltrisol_f16s(out_matrix_ptr, s_ptr, y_ptr, N_TX);
    mempool_Lttrisol_f16s(out_matrix_ptr, y_ptr, x_ptr, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
#endif
  mempool_barrier(num_cores);
  //verify_result(x, Out_x, N_TX, core_id);
  //mempool_barrier(num_cores);
  return;
}

int main() {
  #ifdef SINGLE
  single_core_mimo_mmse();
  #elif defined(PARALLEL)
  parallel_mimo_mmse_cholesky();
  #endif
  return 0;
}
