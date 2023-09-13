// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* This library implements the complex matrix multiplication in multiple
 * different ways. The functions all follow the following format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 */

#include "xpulp/builtins_v2.h"

#define CMATMUL_2x4_LOOP                                                       \
  float sum00_real = 0.0f;                                                     \
  float sum01_real = 0.0f;                                                     \
  float sum02_real = 0.0f;                                                     \
  float sum03_real = 0.0f;                                                     \
  float sum10_real = 0.0f;                                                     \
  float sum11_real = 0.0f;                                                     \
  float sum12_real = 0.0f;                                                     \
  float sum13_real = 0.0f;                                                     \
  float sum00_imag = 0.0f;                                                     \
  float sum01_imag = 0.0f;                                                     \
  float sum02_imag = 0.0f;                                                     \
  float sum03_imag = 0.0f;                                                     \
  float sum10_imag = 0.0f;                                                     \
  float sum11_imag = 0.0f;                                                     \
  float sum12_imag = 0.0f;                                                     \
  float sum13_imag = 0.0f;                                                     \
  for (j = 0; j < N; j += 2) {                                                 \
    v2h a00 = (*(v2h *)&A[2 * ((i + 0) * N + (j + 0))]);                       \
    v2h a01 = (*(v2h *)&A[2 * ((i + 0) * N + (j + 1))]);                       \
    v2h a10 = (*(v2h *)&A[2 * ((i + 1) * N + (j + 0))]);                       \
    v2h a11 = (*(v2h *)&A[2 * ((i + 1) * N + (j + 1))]);                       \
    v2h b00 = (*(v2h *)&B[2 * ((j + 0) * P + (k + 0))]);                       \
    v2h b01 = (*(v2h *)&B[2 * ((j + 0) * P + (k + 1))]);                       \
    v2h b02 = (*(v2h *)&B[2 * ((j + 0) * P + (k + 2))]);                       \
    v2h b03 = (*(v2h *)&B[2 * ((j + 0) * P + (k + 3))]);                       \
    v2h b10 = (*(v2h *)&B[2 * ((j + 1) * P + (k + 0))]);                       \
    v2h b11 = (*(v2h *)&B[2 * ((j + 1) * P + (k + 1))]);                       \
    v2h b12 = (*(v2h *)&B[2 * ((j + 1) * P + (k + 2))]);                       \
    v2h b13 = (*(v2h *)&B[2 * ((j + 1) * P + (k + 3))]);                       \
    v2h a00s, a01s, a10s, a11s;                                                \
    asm volatile("pv.shuffle2.h  %[a00s], %[a00], %[mask];"                    \
                 "pv.shuffle2.h  %[a01s], %[a01], %[mask];"                    \
                 "pv.shuffle2.h  %[a10s], %[a10], %[mask];"                    \
                 "pv.shuffle2.h  %[a11s], %[a11], %[mask];"                    \
                 : [a00s] "+r"(a00s), [a01s] "+r"(a01s), [a10s] "+r"(a10s),    \
                   [a11s] "+r"(a11s)                                           \
                 : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),             \
                   [a11] "r"(a11), [mask] "r"(0x00020003)                      \
                 :);                                                           \
    asm volatile(                                                              \
        "vfdotpex.s.h  %[sum00_imag], %[a00s], %[b00];"                        \
        "vfdotpex.s.h  %[sum10_imag], %[a10s], %[b00];"                        \
        "vfdotpex.s.h  %[sum01_imag], %[a00s], %[b01];"                        \
        "vfdotpex.s.h  %[sum11_imag], %[a10s], %[b01];"                        \
        "vfdotpex.s.h  %[sum02_imag], %[a00s], %[b02];"                        \
        "vfdotpex.s.h  %[sum12_imag], %[a10s], %[b02];"                        \
        "vfdotpex.s.h  %[sum03_imag], %[a00s], %[b03];"                        \
        "vfdotpex.s.h  %[sum13_imag], %[a10s], %[b03];"                        \
        "vfdotpex.s.h  %[sum00_imag], %[a01s], %[b10];"                        \
        "vfdotpex.s.h  %[sum10_imag], %[a11s], %[b10];"                        \
        "vfdotpex.s.h  %[sum01_imag], %[a01s], %[b11];"                        \
        "vfdotpex.s.h  %[sum11_imag], %[a11s], %[b11];"                        \
        "vfdotpex.s.h  %[sum02_imag], %[a01s], %[b12];"                        \
        "vfdotpex.s.h  %[sum12_imag], %[a11s], %[b12];"                        \
        "vfdotpex.s.h  %[sum03_imag], %[a01s], %[b13];"                        \
        "vfdotpex.s.h  %[sum13_imag], %[a11s], %[b13];"                        \
        : [sum00_imag] "+&r"(sum00_imag), [sum01_imag] "+&r"(sum01_imag),      \
          [sum02_imag] "+&r"(sum02_imag), [sum03_imag] "+&r"(sum03_imag),      \
          [sum10_imag] "+&r"(sum10_imag), [sum11_imag] "+&r"(sum11_imag),      \
          [sum12_imag] "+&r"(sum12_imag), [sum13_imag] "+&r"(sum13_imag)       \
        : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),                \
          [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02),    \
          [b03] "r"(b03), [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12),      \
          [b13] "r"(b13)                                                       \
        :);                                                                    \
    asm volatile("xor  %[a00s], %[a00], %[mask];"                              \
                 "xor  %[a01s], %[a01], %[mask];"                              \
                 "xor  %[a10s], %[a10], %[mask];"                              \
                 "xor  %[a11s], %[a11], %[mask];"                              \
                 : [a00s] "+r"(a00s), [a01s] "+r"(a01s), [a10s] "+r"(a10s),    \
                   [a11s] "+r"(a11s)                                           \
                 : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),             \
                   [a11] "r"(a11), [mask] "r"(0x80000000)                      \
                 :);                                                           \
    asm volatile(                                                              \
        "vfdotpex.s.h  %[sum00_real], %[a00s], %[b00];"                        \
        "vfdotpex.s.h  %[sum10_real], %[a10s], %[b00];"                        \
        "vfdotpex.s.h  %[sum01_real], %[a00s], %[b01];"                        \
        "vfdotpex.s.h  %[sum11_real], %[a10s], %[b01];"                        \
        "vfdotpex.s.h  %[sum02_real], %[a00s], %[b02];"                        \
        "vfdotpex.s.h  %[sum12_real], %[a10s], %[b02];"                        \
        "vfdotpex.s.h  %[sum03_real], %[a00s], %[b03];"                        \
        "vfdotpex.s.h  %[sum13_real], %[a10s], %[b03];"                        \
        "vfdotpex.s.h  %[sum00_real], %[a01s], %[b10];"                        \
        "vfdotpex.s.h  %[sum10_real], %[a11s], %[b10];"                        \
        "vfdotpex.s.h  %[sum01_real], %[a01s], %[b11];"                        \
        "vfdotpex.s.h  %[sum11_real], %[a11s], %[b11];"                        \
        "vfdotpex.s.h  %[sum02_real], %[a01s], %[b12];"                        \
        "vfdotpex.s.h  %[sum12_real], %[a11s], %[b12];"                        \
        "vfdotpex.s.h  %[sum03_real], %[a01s], %[b13];"                        \
        "vfdotpex.s.h  %[sum13_real], %[a11s], %[b13];"                        \
        : [sum00_real] "+&r"(sum00_real), [sum01_real] "+&r"(sum01_real),      \
          [sum02_real] "+&r"(sum02_real), [sum03_real] "+&r"(sum03_real),      \
          [sum10_real] "+&r"(sum10_real), [sum11_real] "+&r"(sum11_real),      \
          [sum12_real] "+&r"(sum12_real), [sum13_real] "+&r"(sum13_real)       \
        : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),                \
          [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02),    \
          [b03] "r"(b03), [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12),      \
          [b13] "r"(b13)                                                       \
        :);                                                                    \
  }                                                                            \
  v2h res00, res01, res02, res03;                                              \
  v2h res10, res11, res12, res13;                                              \
  asm volatile(                                                                \
      "vfcpka.h.s %[res00], %[sum00_real], %[sum00_imag];"                     \
      "vfcpka.h.s %[res01], %[sum01_real], %[sum01_imag];"                     \
      "vfcpka.h.s %[res02], %[sum02_real], %[sum02_imag];"                     \
      "vfcpka.h.s %[res03], %[sum03_real], %[sum03_imag];"                     \
      "vfcpka.h.s %[res10], %[sum10_real], %[sum10_imag];"                     \
      "vfcpka.h.s %[res11], %[sum11_real], %[sum11_imag];"                     \
      "vfcpka.h.s %[res12], %[sum12_real], %[sum12_imag];"                     \
      "vfcpka.h.s %[res13], %[sum13_real], %[sum13_imag];"                     \
      : [res00] "+r"(res00), [res01] "+r"(res01), [res02] "+r"(res02),         \
        [res03] "+r"(res03), [res10] "+r"(res10), [res11] "+r"(res11),         \
        [res12] "+r"(res12), [res13] "+r"(res13)                               \
      : [sum00_imag] "r"(sum00_imag), [sum01_imag] "r"(sum01_imag),            \
        [sum02_imag] "r"(sum02_imag), [sum03_imag] "r"(sum03_imag),            \
        [sum10_imag] "r"(sum10_imag), [sum11_imag] "r"(sum11_imag),            \
        [sum12_imag] "r"(sum12_imag), [sum13_imag] "r"(sum13_imag),            \
        [sum00_real] "r"(sum00_real), [sum01_real] "r"(sum01_real),            \
        [sum02_real] "r"(sum02_real), [sum03_real] "r"(sum03_real),            \
        [sum10_real] "r"(sum10_real), [sum11_real] "r"(sum11_real),            \
        [sum12_real] "r"(sum12_real), [sum13_real] "r"(sum13_real)             \
      :);                                                                      \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = res00;                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 1)]) = res01;                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 2)]) = res02;                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 3)]) = res03;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = res10;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = res11;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 2)]) = res12;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 3)]) = res13;

void cmatmul_f16s(__fp16 const *__restrict__ A, __fp16 const *__restrict__ B,
                  __fp16 *__restrict__ C, uint32_t M, uint32_t N, uint32_t P) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = 0; k < P; k++) {
    for (i = 0; i < M; i++) {
      float sum_real = 0.0f;
      float sum_imag = 0.0f;
      for (j = 0; j < N; j++) {
        v2h a = (*(v2h *)&A[2 * (i * N + j)]);
        v2h b = (*(v2h *)&B[2 * (j * P + k)]);
        v2h as;
        asm volatile("pv.shuffle2.h  %[as],       %[a],  %[mask_shuffle];"
                     "vfdotpex.s.h   %[sum_imag], %[as], %[b];"
                     "xor            %[as],       %[a],  %[mask_sign];"
                     "vfdotpex.s.h   %[sum_real], %[as], %[b];"
                     : [sum_real] "+&r"(sum_real), [sum_imag] "+&r"(sum_imag),
                       [as] "+&r"(as)
                     : [a] "r"(a), [b] "r"(b), [mask_shuffle] "r"(0x00020003),
                       [mask_sign] "r"(0x80000000)
                     :);
      }
      v2h res;
      asm volatile("vfcpka.h.s %[res], %[sum_real], %[sum_imag];"
                   : [res] "+r"(res)
                   : [sum_real] "r"(sum_real), [sum_imag] "r"(sum_imag)
                   :);
      (*(v2h *)&C[2 * (i * P + k)]) = res;
    }
  }
  return;
}

void cmatmul_2x4_f16s(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = 0; k < P; k += 4) {
    for (i = 0; i < M; i += 2) {
      CMATMUL_2x4_LOOP;
    }
  }
  return;
}

void cmatmul_2x4_f16p(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t core_id,
                      uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  uint32_t shift_id = core_id % (M / 2);
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = 0; i < shift_id; i += 2) {
      CMATMUL_2x4_LOOP;
    }
    for (i = shift_id; i < M; i += 2) {
      CMATMUL_2x4_LOOP;
    }
  }
  return;
}
