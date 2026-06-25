// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#include "archi_redmule.h"
#include "hal_redmule.h"

#include "baremetal/mempool_matmul_f16.h"
#include "builtins_v2.h"


/**
  @brief         Computes 1D im2col transformation.
  @param[in]     Ci         dimension input channel
  @param[in]     Wi         dimension convolution width
  @param[in]     Wf         dimension filter width
  @param[in]     X          input matrix  size: Cin * Win
  @param[in]     X_im2col   output matrix  size: Cin * Win * Wf
  @return        none
*/

void im2col1d_f16(__fp16 const *__restrict__ X, __fp16 *__restrict__ X_im2col,
                  uint32_t Ci, uint32_t Wi, uint32_t Wf, uint32_t core_id,
                  uint32_t num_cores) {

  if (Wf == 3) {

    for (uint32_t i = core_id; i < Ci; i += num_cores) {
      __fp16 *Out = &X_im2col[i * Wi * 3];
      Out[0 * Wi + 0] = (__fp16)0;
      Out[0 * Wi + 1] = X[i * Wi + 0];
      Out[1 * Wi + 0] = X[i * Wi + 0];
      for (uint32_t j = 1; j < (Wi - 1); j++) {
        __fp16 x = X[i * Wi + j];
        Out[0 * Wi + (j + 1)] = x;
        Out[1 * Wi + (j + 0)] = x;
        Out[2 * Wi + (j - 1)] = x;
      }
      Out[1 * Wi + (Wi - 1)] = X[i * Wi + Wi - 1];
      Out[2 * Wi + (Wi - 2)] = X[i * Wi + Wi - 1];
      Out[2 * Wi + (Wi - 1)] = (__fp16)0;
    }
    mempool_barrier(num_cores);

  } else {

    uint32_t pad = Wf / 2;
    uint32_t i, k; // row, filter
    uint32_t j;    // column

    for (uint32_t i_out = core_id; i_out < Ci * Wf; i_out += num_cores) {
      i = i_out / Wf;
      k = i_out % Wf;
      for (uint32_t j_out = 0; j_out < Wi; j_out++) {
        j = j_out + k;
        if (j >= pad && j < (Wi + pad)) {
          j -= pad;
          volatile __fp16 x = X[i * Wi + j];
          X_im2col[i_out * Wi + j_out] = x;
        } else {
          X_im2col[i_out * Wi + j_out] = (__fp16)0;
        }
      }
    }
    mempool_barrier(num_cores);
  }

  return;
}

/**
  @brief         Computes 1D convolution.
  @param[in]     B      batch size
  @param[in]     Ci     dimension input channel
  @param[in]     Co     dimension output channel
  @param[in]     Wi     dimension convolution width
  @param[in]     Wf     dimension filter width
  @param[in]     X      input matrix  size: loop * Cin * Win
  @param[in]     F      filter matrix size: Cout * Cin * Wf
  @param[out]    Y      output matrix size: loop * Cout * Win
  @param[in]     im2col if 1 execute im2col implementation
  @return        none
*/

void conv1d_f16(__fp16 const *__restrict__ X, __fp16 const *__restrict__ F,
                __fp16 *__restrict__ Y,
                __attribute__((unused)) __fp16 *__restrict__ X_im2col,
                uint32_t B, uint32_t Ci, uint32_t Co, uint32_t Wi, uint32_t Wf,
                uint32_t im2col, uint32_t core_id, uint32_t num_cores) {

  if (im2col) {

    // Transformation
    im2col1d_f16(X, X_im2col, B * Ci, Wi, Wf, core_id, num_cores);
    mempool_stop_benchmark();

    mempool_start_benchmark();
    if (NUM_REDMULE_TILES > 0) {

      uint32_t redmule_id = mempool_get_redmule_id();
      uint32_t num_redmules = mempool_get_redmule_count();
      for (uint32_t ii = redmule_id; ii < B; ii += num_redmules) {
        if (redmule_id < num_redmules) {
          unsigned int I_ptr = (unsigned int)(F);
          unsigned int W_ptr = (unsigned int)(&X_im2col[ii * Ci * Wi * Wf]);
          unsigned int O_ptr = (unsigned int)(&Y[ii * Co * Wi]);
          uint16_t M = (uint16_t)(Co);
          uint16_t N = (uint16_t)(Ci * Wf);
          uint16_t P = (uint16_t)(Wi);
          hwpe_soft_clear();
          mempool_wait(10);
          redmule_cfg(I_ptr, W_ptr, O_ptr, M, N, P, 0, GEMM, Float16);
          mempool_wait(10);
          hwpe_trigger_job();
          mempool_wfi();
        }
      }

    } else {

      uint32_t num_cores_batch = Wi / 2;
      uint32_t core_id_batch = core_id % num_cores_batch;

      uint32_t group_id = core_id / num_cores_batch;
      uint32_t num_groups = num_cores / num_cores_batch;

      for (uint32_t ii = group_id; ii < B; ii += num_groups) {
        __fp16 *W_ptr = &X_im2col[ii * Ci * Wi * Wf];
        __fp16 *O_ptr = &Y[ii * Co * Wi];
        matmul_4x2_parallel_f16vec(F, W_ptr, O_ptr, Co, Ci * Wf, Wi,
                                   core_id_batch, num_cores_batch);
      }
    }

  } else {

    uint32_t pad = Wf / 2;
    for (uint32_t bb = core_id; bb < (B * Co); bb += num_cores) {

      uint32_t ii = bb / Co;
      uint32_t i_out = bb % Co;
      for (uint32_t j_out = 0; j_out < Wi; j_out++) {

        __fp16 sum = 0.0f;
        for (uint32_t k = 0; k < Wf; k++) {
          int32_t j = (int32_t)j_out - (int32_t)pad + (int32_t)k;
          if (j >= 0 && j < (int32_t)Wi) {

            for (uint32_t i = 0; i < Ci; i++) {
              uint32_t x_idx = ii * Ci * Wi + i * Wi + (uint32_t)j;
              uint32_t f_idx = (i_out * Ci + i) * Wf + k;
              asm volatile("fmadd.h %[s], %[x], %[f], %[s];"
                           : [s] "+&r"(sum)
                           : [x] "r"(X[x_idx]), [f] "r"(F[f_idx]));
            }
          }
        }
        Y[(ii * Co + i_out) * Wi + j_out] = sum;
      }
    }
  }

  mempool_barrier(num_cores);
  return;
}
