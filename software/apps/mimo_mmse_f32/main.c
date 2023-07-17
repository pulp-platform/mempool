// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

dump(id, 1);

#include "kernel/mempool_cholesky_f32s.h"
#include "kernel/mempool_linearsolver_f32s.h"
#include "kernel/mempool_mimo_mmse_f32p.h"
#include "kernel/mempool_mimo_mmse_f32s.h"

/* DATA */
#include "data/data_mimo_mmse_f32.h"

#define PARALLEL
//#define SINGLE

#define FOLDED
#define CHOLESKY
//#define JACOBI

#ifdef SINGLE
float ch_matrix[2 * N_TX * N_RX] __attribute__((section(".l1")));
float in_matrix[2 * N_TX * N_TX] __attribute__((section(".l1")));
float out_matrix[2 * N_TX * N_TX] __attribute__((section(".l1")));
float sigma[2 * N_TX] __attribute__((section(".l1")));
float b[2 * N_RX] __attribute__((section(".l1")));

float s[2 * N_TX] __attribute__((section(".l1")));
float x[2 * N_TX] __attribute__((section(".l1")));
float y[2 * N_TX] __attribute__((section(".l1")));
#endif

#ifdef PARALLEL
float in_matrix[2 * N_TX * N_TX * N_ITR]
    __attribute__((section(".l1_prio"), aligned(N_BANKS)));
float out_matrix[2 * N_TX * N_TX * N_ITR]
    __attribute__((section(".l1_prio"), aligned(N_BANKS)));
float s[2 * N_TX * N_ITR]
    __attribute__((section(".l1_prio"), aligned(N_BANKS)));
float x[2 * N_TX * N_ITR]
    __attribute__((section(".l1_prio"), aligned(N_BANKS)));
float y[2 * N_TX * N_ITR]
    __attribute__((section(".l1_prio"), aligned(N_BANKS)));

float ch_matrix[2 * N_TX * N_RX * N_ITR] __attribute__((section(".l1_prio")));
float b[2 * N_RX * N_ITR] __attribute__((section(".l1_prio")));
float sigma[N_TX * N_ITR] __attribute__((section(".l1_prio")));
#endif

void initialize(float *matrix, float *data, uint32_t dim, uint32_t core_id,
                uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i += num_cores) {
    matrix[i] = data[i];
  }
  mempool_barrier(num_cores);
  return;
}

void initialize_zeros(float *matrix, uint32_t dim, uint32_t core_id,
                      uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i += num_cores) {
    matrix[i] = 0.0f;
  }
  mempool_barrier(num_cores);
  return;
}

void verify_result(float *pRes, float *pExp, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {
      float error;
      float exp = pExp[i];
      float res = pRes[i];
      asm volatile("fsub.s %[error], %[res], %[exp];"
                   : [error] "=&r"(error)
                   : [res] "r"(res), [exp] "r"(exp)
                   :);
      if (*(int32_t *)&error != 0) {
        printf("(%d): 0x%08x - 0x%08x - 0x%08x\n", i / 2, *(int32_t *)&error,
               *(int32_t *)&exp, *(int32_t *)&res);
      }
    }
  }
}

void write_result(float *pRes, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {

      float in = pRes[i];
      dump_id(*(uint32_t *)&in);
    }
  }
}

#ifdef SINGLE

// Driver program
void single_core_mimo_mmse_cholesky() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX * N_TX, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX * N_TX, core_id, num_cores);
  initialize_zeros(out_matrix, N_TX * N_TX, core_id, num_cores);
  /* Initialize vectors */
  initialize(sigma, In_sigma, N_TX, core_id, num_cores);
  initialize(b, In_b, N_RX, core_id, num_cores);

  initialize_zeros(s, N_TX, core_id, num_cores);
  initialize_zeros(y, N_TX, core_id, num_cores);
  initialize_zeros(x, N_TX, core_id, num_cores);

  /* Benchmark */
  if (core_id == 0) {

    mempool_start_benchmark();
    mempool_hermitian_f32s(ch_matrix, in_matrix, sigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f32s(ch_matrix, b, s, N_RX, N_TX, 0);
    mempool_stop_benchmark();

    mempool_start_benchmark();
    mempool_cholesky_f32s(in_matrix, out_matrix, N_TX);
    mempool_Ltrisol_f32s(out_matrix, s, y, N_TX);
    mempool_Lttrisol_f32s(out_matrix, y, x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  verify_result(x, Out_x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}

// Driver program
void single_core_mimo_mmse_jacobi() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX * N_TX, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX * N_TX, core_id, num_cores);
  /* Initialize vectors */
  initialize(sigma, In_sigma, N_TX, core_id, num_cores);
  initialize(b, In_b, N_RX, core_id, num_cores);
  initialize_zeros(s, N_TX, core_id, num_cores);
  initialize_zeros(x, N_TX, core_id, num_cores);

  /* Benchmark */
  if (core_id == 0) {

    mempool_start_benchmark();
    mempool_hermitian_f32s(ch_matrix, in_matrix, sigma, N_RX, N_TX, 0, 0);
    mempool_MVP_conjtransp_f32s(ch_matrix, b, s, N_RX, N_TX, 0);
    mempool_stop_benchmark();

    mempool_start_benchmark();
    mempool_jacobi_f32s(in_matrix, s, x, 0.005f, N_TX, 20U);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);
  verify_result(x, Out_x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}

#endif

#ifdef PARALLEL

// Driver program
void parallel_mimo_mmse_cholesky() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX * N_TX * N_ITR, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX * N_TX * N_ITR, core_id, num_cores);
  initialize_zeros(out_matrix, N_TX * N_TX * N_ITR, core_id, num_cores);
  /* Initialize vectors */
  initialize(sigma, In_sigma, N_TX * N_ITR / 2, core_id, num_cores);
  initialize(b, In_b, N_RX * N_ITR, core_id, num_cores);

  initialize_zeros(s, N_TX * N_ITR, core_id, num_cores);
  initialize_zeros(y, N_TX * N_ITR, core_id, num_cores);
  initialize_zeros(x, N_TX * N_ITR, core_id, num_cores);

  /* Benchmark */

#ifdef FOLDED

  mempool_start_benchmark();
  // Each iteration is assigned to a pool of processors
  // In a pool each PE gets a column of the H matrix, accumulating a row of the
  // output matrix
  uint32_t pool_id = core_id / N_TX;
  uint32_t num_pools = num_cores / N_TX;
  for (uint32_t itr = pool_id; itr < N_ITR; itr += num_pools) {
    // Inputs
    float *ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    float *sigma_ptr = sigma + itr * N_TX;
    // Intermediate results and outputs
    float *in_matrix_ptr = in_matrix + (itr % num_pools) * N_TX +
                           (itr / num_pools) * (2 * N_TX * N_BANKS);
    mempool_hermitian_f32p(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX, N_TX,
                           1, 0, core_id % N_TX, N_TX);
  }
  mempool_stop_benchmark();
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    // Inputs
    float *ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    float *b_ptr = b + itr * (2 * N_RX);
    // Intermediate results and outputs
    float *in_matrix_ptr = in_matrix + (itr % num_cores) * N_TX +
                           (itr / num_cores) * (2 * N_TX * N_BANKS);
    float *out_matrix_ptr = out_matrix + (itr % num_cores) * N_TX +
                            (itr / num_cores) * (2 * N_TX * N_BANKS);
    float *s_ptr =
        s + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    float *y_ptr =
        y + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    float *x_ptr =
        x + (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_BANKS);
    mempool_MVP_conjtransp_f32s(ch_matrix_ptr, b_ptr, s_ptr, N_RX, N_TX, 1);
    mempool_cholesky_folded_f32s(in_matrix_ptr, out_matrix_ptr, N_TX);
    mempool_Ltrisol_folded_f32s(out_matrix_ptr, s_ptr, y_ptr, N_TX);
    mempool_Lttrisol_folded_f32s(out_matrix_ptr, y_ptr, x_ptr, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();

  //  mempool_start_benchmark();
  //  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
  //    // Inputs
  //    float* ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
  //    float* sigma_ptr = sigma + itr * N_TX;
  //    float* b_ptr = b + itr * (2 * N_RX);
  //    // Intermediate results and outputs
  //    float* in_matrix_ptr = in_matrix + (itr % num_cores) * N_TX + (itr /
  //    num_cores) * (2 * N_TX * N_BANKS); float* out_matrix_ptr = out_matrix +
  //    (itr % num_cores) * N_TX + (itr / num_cores) * (2 * N_TX * N_BANKS);
  //    float* s_ptr = s + (itr % num_cores) * N_TX + (itr / num_cores) * (2 *
  //    N_BANKS); float* y_ptr = y + (itr % num_cores) * N_TX + (itr /
  //    num_cores) * (2 * N_BANKS); float* x_ptr = x + (itr % num_cores) * N_TX
  //    + (itr / num_cores) * (2 * N_BANKS);
  //    mempool_hermitian_f32s(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX,
  //    N_TX, 1, 0); mempool_MVP_conjtransp_f32s(ch_matrix_ptr, b_ptr, s_ptr,
  //    N_RX, N_TX, 1); mempool_cholesky_folded_f32s(in_matrix_ptr,
  //    out_matrix_ptr, N_TX); mempool_Ltrisol_folded_f32s(out_matrix_ptr,
  //    s_ptr, y_ptr, N_TX); mempool_Lttrisol_folded_f32s(out_matrix_ptr, y_ptr,
  //    x_ptr, N_TX);
  //  }
  //  mempool_log_barrier(2, core_id);
  //  mempool_stop_benchmark();

#else

  mempool_start_benchmark();
  // Each iteration is assigned to a pool of processors
  // In a pool each PE gets a column of the H matrix, accumulating a row of the
  // output matrix
  uint32_t pool_id = core_id / N_TX;
  uint32_t num_pools = num_cores / N_TX;
  for (uint32_t itr = pool_id; itr < N_ITR; itr += num_pools) {
    float *ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    float *in_matrix_ptr = in_matrix + itr * (2 * N_TX * N_TX);
    float *sigma_ptr = sigma + itr * N_TX;
    mempool_hermitian_f32p(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX, N_TX,
                           0, 0, core_id % N_TX, N_TX);
  }
  mempool_stop_benchmark();
  mempool_start_benchmark();
  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
    // Inputs
    float *ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
    float *sigma_ptr = sigma + itr * N_TX;
    float *b_ptr = b + itr * (2 * N_RX);
    // Intermediate results and outputs
    float *in_matrix_ptr = in_matrix + itr * (2 * N_TX * N_TX);
    float *out_matrix_ptr = out_matrix + itr * (2 * N_TX * N_TX);
    float *s_ptr = s + itr * (2 * N_TX);
    float *y_ptr = y + itr * (2 * N_TX);
    float *x_ptr = x + itr * (2 * N_TX);
    mempool_MVP_conjtransp_f32s(ch_matrix_ptr, b_ptr, s_ptr, N_RX, N_TX, 0);
    mempool_cholesky_f32s(in_matrix_ptr, out_matrix_ptr, N_TX);
    mempool_Ltrisol_f32s(out_matrix_ptr, s_ptr, y_ptr, N_TX);
    mempool_Lttrisol_f32s(out_matrix_ptr, y_ptr, x_ptr, N_TX);
  }
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();

  //  // Each iteration is assigned to a pool of processors
  //  mempool_start_benchmark();
  //  for (uint32_t itr = core_id; itr < N_ITR; itr += num_cores) {
  //    // Inputs
  //    float* ch_matrix_ptr = ch_matrix + itr * (2 * N_TX * N_RX);
  //    float* sigma_ptr = sigma + itr * N_TX;
  //    float* b_ptr = b + itr * (2 * N_RX);
  //    // Intermediate results and outputs
  //    float* in_matrix_ptr = in_matrix + itr * (2 * N_TX * N_TX);
  //    float* out_matrix_ptr = out_matrix + itr * (2 * N_TX * N_TX);
  //    float* s_ptr = s + itr * (2 * N_TX);
  //    float* y_ptr = y + itr * (2 * N_TX);
  //    float* x_ptr = x + itr * (2 * N_TX);
  //    mempool_hermitian_f32s(ch_matrix_ptr, in_matrix_ptr, sigma_ptr, N_RX,
  //    N_TX, 0, 0); mempool_MVP_conjtransp_f32s(ch_matrix_ptr, b_ptr, s_ptr,
  //    N_RX, N_TX, 0); mempool_cholesky_f32s(in_matrix_ptr, out_matrix_ptr,
  //    N_TX); mempool_Ltrisol_f32s(out_matrix_ptr, s_ptr, y_ptr, N_TX);
  //    mempool_Lttrisol_f32s(out_matrix_ptr, y_ptr, x_ptr, N_TX);
  //  }
  //  mempool_log_barrier(2, core_id);
  //  mempool_stop_benchmark();

#endif
  mempool_barrier(num_cores);
  return;
}

#endif

int main() {

#ifdef SINGLE
#if defined(CHOLESKY)
  single_core_mimo_mmse_cholesky();
#elif defined(JACOBI)
  single_core_mimo_mmse_jacobi();
#endif
#endif

#ifdef PARALLEL
  parallel_mimo_mmse_cholesky();
#endif

  return 0;
}
