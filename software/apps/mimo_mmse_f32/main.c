// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "mimo_mmse_f32.h"

/* DATA */
#include "data_mimo_mmse_f32.h"

dump(res,1);


#define CHOLESKY
//#define JACOBI

float ch_matrix[2 * N_TX * N_RX]    __attribute__((section(".l1")));
float in_matrix[2 * N_TX * N_TX]    __attribute__((section(".l1")));
float out_matrix[2 * N_TX * N_TX]   __attribute__((section(".l1")));
float sigma[2 * N_TX]   __attribute__((section(".l1")));
float b[2 * N_RX]   __attribute__((section(".l1")));

float s[2 * N_TX]   __attribute__((section(".l1")));
float x[2 * N_TX]   __attribute__((section(".l1")));
float y[2 * N_TX]   __attribute__((section(".l1")));

void initialize(float *matrix, float *data, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i++) {
    matrix[i] = data[i];
  }
  mempool_barrier(num_cores);
  return;
}

void initialize_zeros(float *matrix, uint32_t dim, uint32_t core_id, uint32_t num_cores) {
  uint32_t i = 0;
  for (i = core_id; i < 2 * dim; i++) {
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
      asm volatile(
        "fsub.s %[error], %[res], %[exp];"
        : [error] "=&r"(error)
        : [res] "r"(res), [exp] "r"(exp)
        : );
      if (*(int32_t*)&error != 0) {
        printf("(%d): 0x%08x - 0x%08x - 0x%08x\n", i / 2, *(int32_t*)&error, *(int32_t*)&exp, *(int32_t*)&res);
      }
    }
  }
}

void write_result(float *pRes, uint32_t dim, uint32_t core_id) {
  if (core_id == 0) {
    for (uint32_t i = 0; i < 2 * dim; i++) {

      float in = pRes[i];
      dump_res(*(uint32_t*)&in);

    }
  }
}

// Driver program
void single_core_mimo_mmse_cholesky() {

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
    mempool_start_benchmark();
    mempool_hermitian_f32s(ch_matrix, in_matrix, sigma, N_RX, N_TX);
    mempool_MVP_conjtransp_f32s(ch_matrix, b, s, N_RX, N_TX);

    mempool_cholesky_f32s(in_matrix, out_matrix, N_TX);
    mempool_Ltrisol_f32s(out_matrix, s, y, N_TX);
    mempool_Lttrisol_f32s(out_matrix, y, x, N_TX);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  // verify_result(in_matrix, In_G, N_TX*N_TX, core_id);
  // verify_result(out_matrix, Out_L,  N_TX*N_TX, core_id);
  // verify_result(s, Out_s, N_TX, core_id);
  // verify_result(y, Out_y, N_TX, core_id);
  // verify_result(x, Out_x, N_TX, core_id);
  write_result(x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}

// Driver program
void single_core_mimo_mmse_jacobi() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id); // Initialize barrier and synchronize//

  /* Initialize matrices */
  initialize(ch_matrix, In_H, N_RX*N_TX, core_id, num_cores);
  initialize_zeros(in_matrix, N_TX*N_TX, core_id, num_cores);
  /* Initialize vectors */
  initialize(sigma, In_sigma, N_TX, core_id, num_cores);
  initialize(b, In_b, N_RX, core_id, num_cores);
  initialize_zeros(s, N_TX, core_id, num_cores);
  initialize_zeros(x, N_TX, core_id, num_cores);

  /* Benchmark */
  if (core_id == 0) {
    mempool_start_benchmark();
    mempool_hermitian_f32s(ch_matrix, in_matrix, sigma, N_RX, N_TX);
    mempool_stop_benchmark();
    mempool_start_benchmark();
    mempool_MVP_conjtransp_f32s(ch_matrix, b, s, N_RX, N_TX);
    mempool_stop_benchmark();
    mempool_start_benchmark();
    mempool_jacobi_f32s(in_matrix, s, x, 0.005f, N_TX, 20U);
    mempool_stop_benchmark();
  }
  mempool_barrier(num_cores);

  // verify_result(in_matrix, In_G, N_TX*N_TX, core_id);
  // verify_result(s, Out_s, N_TX, core_id);
  // verify_result(y, Out_y, N_TX, core_id);
  // verify_result(x, Out_x, N_TX, core_id);
  mempool_barrier(num_cores);
  return;
}


int main() {

  #if defined(CHOLESKY)
  single_core_mimo_mmse_cholesky();
  #elif defined(JACOBI)
  single_core_mimo_mmse_jacobi();
  #endif

  return 0;
}
