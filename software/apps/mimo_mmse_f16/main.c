// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "mimo_mmse_f16.h"

/* DATA */
//#include "data_choldec_f16.h"
//#include "data_Axb_f16.h"
#include "data_mimo_mmse_f16.h"

dump(res,1);

__fp16 ch_matrix[2 * N_TX * N_RX]    __attribute__((section(".l1")));
__fp16 in_matrix[2 * N_TX * N_TX]    __attribute__((section(".l1")));
__fp16 out_matrix[2 * N_TX * N_TX]   __attribute__((section(".l1")));
__fp16 sigma[2 * N_TX]   __attribute__((section(".l1")));
__fp16 b[2 * N_RX]   __attribute__((section(".l1")));

__fp16 s[2 * N_TX]   __attribute__((section(".l1")));
__fp16 x[2 * N_TX]   __attribute__((section(".l1")));
__fp16 y[2 * N_TX]   __attribute__((section(".l1")));

void initialize(__fp16 *matrix, __fp16 *data, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i++) {
    matrix[i] = data[i];
  }
  mempool_barrier(num_cores);
  return;
}

void initialize_zeros(__fp16 *matrix, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i++) {
    matrix[i] = (__fp16) (0x0000);
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
      dump_res(*(uint32_t*)&cvt_out);

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

  initialize_zeros(s, N_TX, core_id, num_cores);
  initialize_zeros(y, N_TX, core_id, num_cores);
  initialize_zeros(x, N_TX, core_id, num_cores);


  /* Benchmark */
  if (core_id == 0) {
    /* Computation of the Hermitian matrix */
    mempool_start_benchmark();
    mempool_hermitian_f16s(ch_matrix, in_matrix, sigma, N_RX, N_TX);
    mempool_stop_benchmark();
    /* Computation of the H^H*b vector */
    mempool_start_benchmark();
    mempool_MVP_conjtransp_f16s(ch_matrix, b, s, N_RX, N_TX);
    mempool_stop_benchmark();
    /* Cholesky decomposition */
    mempool_start_benchmark();
    mempool_cholesky_f16s(in_matrix, out_matrix, N_TX);
    mempool_stop_benchmark();
    /* Solution of L*y = s */
    mempool_start_benchmark();
    mempool_Ltrisol_f16s(out_matrix, s, y, N_TX);
    mempool_stop_benchmark();
    /* Solution of L^T*s = b */
    mempool_start_benchmark();
    mempool_Lttrisol_f16s(out_matrix, y, x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  //verify_result(in_matrix, In_G, N_TX*N_TX, core_id);
  //verify_result(out_matrix, Out_L,  N_TX*N_TX, core_id);
  //verify_result(s, Out_s, N_TX, core_id);
  verify_result(x, Out_x, N_TX, core_id);
  //write_result(x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}


int main() {
  // single_core_cholesky();
  // single_core_Axb();
  single_core_mimo_mmse();
  return 0;
}
