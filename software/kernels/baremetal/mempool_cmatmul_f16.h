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

#include "builtins_v2.h"

#define CMATMUL_2x2_LOOP                                                       \
  float sum00_real = 0.0f;                                                     \
  float sum01_real = 0.0f;                                                     \
  float sum10_real = 0.0f;                                                     \
  float sum11_real = 0.0f;                                                     \
  float sum00_imag = 0.0f;                                                     \
  float sum01_imag = 0.0f;                                                     \
  float sum10_imag = 0.0f;                                                     \
  float sum11_imag = 0.0f;                                                     \
  v2h a00s, a01s, a10s, a11s;                                                  \
  v2h res00, res01, res10, res11;                                              \
  for (j = 0; j < N; j += 2) {                                                 \
    v2h a00 = *(v2h *)&A[2 * ((i + 0) * N + (j + 0))];                         \
    v2h a01 = *(v2h *)&A[2 * ((i + 0) * N + (j + 1))];                         \
    v2h a10 = *(v2h *)&A[2 * ((i + 1) * N + (j + 0))];                         \
    v2h a11 = *(v2h *)&A[2 * ((i + 1) * N + (j + 1))];                         \
    v2h b00 = *(v2h *)&B[2 * ((j + 0) * P + (k + 0))];                         \
    v2h b01 = *(v2h *)&B[2 * ((j + 0) * P + (k + 1))];                         \
    v2h b10 = *(v2h *)&B[2 * ((j + 1) * P + (k + 0))];                         \
    v2h b11 = *(v2h *)&B[2 * ((j + 1) * P + (k + 1))];                         \
    asm volatile("pv.shuffle2.h  %[a00s], %[a00], %[mask];"                    \
                 "pv.shuffle2.h  %[a10s], %[a10], %[mask];"                    \
                 "pv.shuffle2.h  %[a01s], %[a01], %[mask];"                    \
                 "pv.shuffle2.h  %[a11s], %[a11], %[mask];"                    \
                 : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s), \
                   [a11s] "=&r"(a11s)                                          \
                 : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),             \
                   [a11] "r"(a11), [mask] "r"(0x00020003)                      \
                 :);                                                           \
    asm volatile(                                                              \
        "vfdotpex.s.h  %[sum00_imag], %[a00s], %[b00];"                        \
        "vfdotpex.s.h  %[sum10_imag], %[a10s], %[b00];"                        \
        "vfdotpex.s.h  %[sum01_imag], %[a00s], %[b01];"                        \
        "vfdotpex.s.h  %[sum11_imag], %[a10s], %[b01];"                        \
        "vfdotpex.s.h  %[sum00_imag], %[a01s], %[b10];"                        \
        "vfdotpex.s.h  %[sum10_imag], %[a11s], %[b10];"                        \
        "vfdotpex.s.h  %[sum01_imag], %[a01s], %[b11];"                        \
        "vfdotpex.s.h  %[sum11_imag], %[a11s], %[b11];"                        \
        : [sum00_imag] "+&r"(sum00_imag), [sum01_imag] "+&r"(sum01_imag),      \
          [sum10_imag] "+&r"(sum10_imag), [sum11_imag] "+&r"(sum11_imag)       \
        : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),                \
          [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10),    \
          [b11] "r"(b11)                                                       \
        :);                                                                    \
    asm volatile("xor  %[a00s], %[a00], %[mask];"                              \
                 "xor  %[a10s], %[a10], %[mask];"                              \
                 "xor  %[a01s], %[a01], %[mask];"                              \
                 "xor  %[a11s], %[a11], %[mask];"                              \
                 : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s), \
                   [a11s] "=&r"(a11s)                                          \
                 : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),             \
                   [a11] "r"(a11), [mask] "r"(0x00008000)                      \
                 :);                                                           \
    asm volatile(                                                              \
        "vfdotpex.s.h  %[sum00_real], %[a00s], %[b00];"                        \
        "vfdotpex.s.h  %[sum10_real], %[a10s], %[b00];"                        \
        "vfdotpex.s.h  %[sum01_real], %[a00s], %[b01];"                        \
        "vfdotpex.s.h  %[sum11_real], %[a10s], %[b01];"                        \
        "vfdotpex.s.h  %[sum00_real], %[a01s], %[b10];"                        \
        "vfdotpex.s.h  %[sum10_real], %[a11s], %[b10];"                        \
        "vfdotpex.s.h  %[sum01_real], %[a01s], %[b11];"                        \
        "vfdotpex.s.h  %[sum11_real], %[a11s], %[b11];"                        \
        : [sum00_real] "+&r"(sum00_real), [sum01_real] "+&r"(sum01_real),      \
          [sum10_real] "+&r"(sum10_real), [sum11_real] "+&r"(sum11_real)       \
        : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),                \
          [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10),    \
          [b11] "r"(b11)                                                       \
        :);                                                                    \
  }                                                                            \
  asm volatile("vfcpka.h.s %[res00], %[sum00_imag], %[sum00_real];"            \
               "vfcpka.h.s %[res01], %[sum01_imag], %[sum01_real];"            \
               "vfcpka.h.s %[res10], %[sum10_imag], %[sum10_real];"            \
               "vfcpka.h.s %[res11], %[sum11_imag], %[sum11_real];"            \
               : [res00] "=r"(res00), [res01] "=r"(res01),                     \
                 [res10] "=r"(res10), [res11] "=r"(res11)                      \
               : [sum00_imag] "r"(sum00_imag), [sum01_imag] "r"(sum01_imag),   \
                 [sum10_imag] "r"(sum10_imag), [sum11_imag] "r"(sum11_imag),   \
                 [sum00_real] "r"(sum00_real), [sum01_real] "r"(sum01_real),   \
                 [sum10_real] "r"(sum10_real), [sum11_real] "r"(sum11_real)    \
               :);                                                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = res00;                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 1)]) = res01;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = res10;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = res11;

#define CMATMUL_2x4_LOOP                                                       \
  float register volatile sum00_real = 0.0f;                                   \
  float register volatile sum01_real = 0.0f;                                   \
  float register volatile sum02_real = 0.0f;                                   \
  float register volatile sum03_real = 0.0f;                                   \
  float register volatile sum10_real = 0.0f;                                   \
  float register volatile sum11_real = 0.0f;                                   \
  float register volatile sum12_real = 0.0f;                                   \
  float register volatile sum13_real = 0.0f;                                   \
  float register volatile sum00_imag = 0.0f;                                   \
  float register volatile sum01_imag = 0.0f;                                   \
  float register volatile sum02_imag = 0.0f;                                   \
  float register volatile sum03_imag = 0.0f;                                   \
  float register volatile sum10_imag = 0.0f;                                   \
  float register volatile sum11_imag = 0.0f;                                   \
  float register volatile sum12_imag = 0.0f;                                   \
  float register volatile sum13_imag = 0.0f;                                   \
  v2h a00s, a01s, a10s, a11s;                                                  \
  for (j = 0; j < N; j += 2) {                                                 \
    v2h a00 = A[(i + 0) * N + (j + 0)];                                        \
    v2h a01 = A[(i + 0) * N + (j + 1)];                                        \
    v2h a10 = A[(i + 1) * N + (j + 0)];                                        \
    v2h a11 = A[(i + 1) * N + (j + 1)];                                        \
    v2h b00 = B[(j + 0) * P + (k + 0)];                                        \
    v2h b01 = B[(j + 0) * P + (k + 1)];                                        \
    v2h b02 = B[(j + 0) * P + (k + 2)];                                        \
    v2h b03 = B[(j + 0) * P + (k + 3)];                                        \
    v2h b10 = B[(j + 1) * P + (k + 0)];                                        \
    v2h b11 = B[(j + 1) * P + (k + 1)];                                        \
    v2h b12 = B[(j + 1) * P + (k + 2)];                                        \
    v2h b13 = B[(j + 1) * P + (k + 3)];                                        \
    asm volatile(                                                              \
        "pv.shuffle2.h  %[a00s], %[a00], %[mask];"                             \
        "pv.shuffle2.h  %[a10s], %[a10], %[mask];"                             \
        "pv.shuffle2.h  %[a01s], %[a01], %[mask];"                             \
        "pv.shuffle2.h  %[a11s], %[a11], %[mask];"                             \
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
        : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s),          \
          [a11s] "=&r"(a11s), [sum00_imag] "+&r"(sum00_imag),                  \
          [sum01_imag] "+&r"(sum01_imag), [sum02_imag] "+&r"(sum02_imag),      \
          [sum03_imag] "+&r"(sum03_imag), [sum10_imag] "+&r"(sum10_imag),      \
          [sum11_imag] "+&r"(sum11_imag), [sum12_imag] "+&r"(sum12_imag),      \
          [sum13_imag] "+&r"(sum13_imag)                                       \
        : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),      \
          [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),      \
          [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13),      \
          [mask] "r"(0x00020003)                                               \
        :);                                                                    \
    asm volatile(                                                              \
        "xor  %[a00s], %[a00], %[maskn];"                                      \
        "xor  %[a10s], %[a10], %[maskn];"                                      \
        "xor  %[a01s], %[a01], %[maskn];"                                      \
        "xor  %[a11s], %[a11], %[maskn];"                                      \
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
        : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s),          \
          [a11s] "=&r"(a11s), [sum00_real] "+&r"(sum00_real),                  \
          [sum01_real] "+&r"(sum01_real), [sum02_real] "+&r"(sum02_real),      \
          [sum03_real] "+&r"(sum03_real), [sum10_real] "+&r"(sum10_real),      \
          [sum11_real] "+&r"(sum11_real), [sum12_real] "+&r"(sum12_real),      \
          [sum13_real] "+&r"(sum13_real)                                       \
        : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),      \
          [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),      \
          [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13),      \
          [maskn] "r"(0x00008000)                                              \
        :);                                                                    \
  }                                                                            \
  asm volatile(                                                                \
      "vfcpka.h.s %[sum00_real], %[sum00_imag], %[sum00_real];"                \
      "vfcpka.h.s %[sum01_real], %[sum01_imag], %[sum01_real];"                \
      "vfcpka.h.s %[sum02_real], %[sum02_imag], %[sum02_real];"                \
      "vfcpka.h.s %[sum03_real], %[sum03_imag], %[sum03_real];"                \
      "vfcpka.h.s %[sum10_real], %[sum10_imag], %[sum10_real];"                \
      "vfcpka.h.s %[sum11_real], %[sum11_imag], %[sum11_real];"                \
      "vfcpka.h.s %[sum12_real], %[sum12_imag], %[sum12_real];"                \
      "vfcpka.h.s %[sum13_real], %[sum13_imag], %[sum13_real];"                \
      : [sum00_real] "+&r"(sum00_real), [sum01_real] "+&r"(sum01_real),        \
        [sum02_real] "+&r"(sum02_real), [sum03_real] "+&r"(sum03_real),        \
        [sum10_real] "+&r"(sum10_real), [sum11_real] "+&r"(sum11_real),        \
        [sum12_real] "+&r"(sum12_real), [sum13_real] "+&r"(sum13_real)         \
      : [sum00_imag] "r"(sum00_imag), [sum01_imag] "r"(sum01_imag),            \
        [sum02_imag] "r"(sum02_imag), [sum03_imag] "r"(sum03_imag),            \
        [sum10_imag] "r"(sum10_imag), [sum11_imag] "r"(sum11_imag),            \
        [sum12_imag] "r"(sum12_imag), [sum13_imag] "r"(sum13_imag)             \
      :);                                                                      \
  C[(i + 0) * P + k + 0] = (v2h)sum00_real;                                    \
  C[(i + 0) * P + k + 1] = (v2h)sum01_real;                                    \
  C[(i + 0) * P + k + 2] = (v2h)sum02_real;                                    \
  C[(i + 0) * P + k + 3] = (v2h)sum03_real;                                    \
  C[(i + 1) * P + k + 0] = (v2h)sum10_real;                                    \
  C[(i + 1) * P + k + 1] = (v2h)sum11_real;                                    \
  C[(i + 1) * P + k + 2] = (v2h)sum12_real;                                    \
  C[(i + 1) * P + k + 3] = (v2h)sum13_real;

/**************************************************************************/
/**************************************************************************/
// COMPLEX DOTP INSTRUCTIONS

#define CMATMUL_CDOTP_1x1_LOOP                                                 \
  v2h sum = (v2h)0.0f;                                                         \
  for (j = 0; j < N; j++) {                                                    \
    v2h a = *(v2h *)&A[2 * (i * M + j)];                                       \
    v2h b = *(v2h *)&B[2 * (j * P + k)];                                       \
    asm volatile("fcdotpex.s.h  %[sum], %[a], %[b];"                           \
                 : [sum] "+&r"(sum)                                            \
                 : [a] "r"(a), [b] "r"(b)                                      \
                 :);                                                           \
  }                                                                            \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = sum;

#define CMATMUL_CDOTP_2x2_LOOP                                                 \
  v2h sum00 = (v2h)0.0f;                                                       \
  v2h sum01 = (v2h)0.0f;                                                       \
  v2h sum10 = (v2h)0.0f;                                                       \
  v2h sum11 = (v2h)0.0f;                                                       \
  for (j = 0; j < N; j += 2) {                                                 \
    v2h a00 = *(v2h *)&A[2 * ((i + 0) * M + (j + 0))];                         \
    v2h a01 = *(v2h *)&A[2 * ((i + 0) * M + (j + 1))];                         \
    v2h a10 = *(v2h *)&A[2 * ((i + 1) * M + (j + 0))];                         \
    v2h a11 = *(v2h *)&A[2 * ((i + 1) * M + (j + 1))];                         \
    v2h b00 = *(v2h *)&B[2 * ((j + 0) * P + (k + 0))];                         \
    v2h b01 = *(v2h *)&B[2 * ((j + 0) * P + (k + 1))];                         \
    v2h b10 = *(v2h *)&B[2 * ((j + 1) * P + (k + 0))];                         \
    v2h b11 = *(v2h *)&B[2 * ((j + 1) * P + (k + 1))];                         \
    asm volatile(                                                              \
        "fcdotpex.s.h  %[sum00], %[a00], %[b00];"                              \
        "fcdotpex.s.h  %[sum10], %[a10], %[b00];"                              \
        "fcdotpex.s.h  %[sum01], %[a00], %[b01];"                              \
        "fcdotpex.s.h  %[sum11], %[a10], %[b01];"                              \
        "fcdotpex.s.h  %[sum00], %[a01], %[b10];"                              \
        "fcdotpex.s.h  %[sum10], %[a11], %[b10];"                              \
        "fcdotpex.s.h  %[sum01], %[a01], %[b11];"                              \
        "fcdotpex.s.h  %[sum11], %[a11], %[b11];"                              \
        : [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum10] "+&r"(sum10),    \
          [sum11] "+&r"(sum11)                                                 \
        : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),      \
          [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10), [b11] "r"(b11)       \
        :);                                                                    \
  }                                                                            \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = sum00;                             \
  (*(v2h *)&C[2 * ((i + 0) * P + k + 1)]) = sum01;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = sum10;                             \
  (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = sum11;

#define CMATMUL_CDOTP_2x4_LOOP                                                 \
  v2h sum00 = (v2h)0.0f;                                                       \
  v2h sum01 = (v2h)0.0f;                                                       \
  v2h sum02 = (v2h)0.0f;                                                       \
  v2h sum03 = (v2h)0.0f;                                                       \
  v2h sum10 = (v2h)0.0f;                                                       \
  v2h sum11 = (v2h)0.0f;                                                       \
  v2h sum12 = (v2h)0.0f;                                                       \
  v2h sum13 = (v2h)0.0f;                                                       \
  for (j = 0; j < N; j += 2) {                                                 \
    v2h a00 = A[i * M + j + 0];                                                \
    v2h a01 = A[i * M + j + 1];                                                \
    v2h a10 = A[(i + 1) * M + j + 0];                                          \
    v2h a11 = A[(i + 1) * M + j + 1];                                          \
    v2h b00 = B[j * P + k + 0];                                                \
    v2h b01 = B[j * P + k + 1];                                                \
    v2h b02 = B[j * P + k + 2];                                                \
    v2h b03 = B[j * P + k + 3];                                                \
    v2h b10 = B[(j + 1) * P + k + 0];                                          \
    v2h b11 = B[(j + 1) * P + k + 1];                                          \
    v2h b12 = B[(j + 1) * P + k + 2];                                          \
    v2h b13 = B[(j + 1) * P + k + 3];                                          \
    asm volatile(                                                              \
        "fcdotpex.s.h  %[sum00], %[a00], %[b00];"                              \
        "fcdotpex.s.h  %[sum10], %[a10], %[b00];"                              \
        "fcdotpex.s.h  %[sum01], %[a00], %[b01];"                              \
        "fcdotpex.s.h  %[sum11], %[a10], %[b01];"                              \
        "fcdotpex.s.h  %[sum02], %[a00], %[b02];"                              \
        "fcdotpex.s.h  %[sum12], %[a10], %[b02];"                              \
        "fcdotpex.s.h  %[sum03], %[a00], %[b03];"                              \
        "fcdotpex.s.h  %[sum13], %[a10], %[b03];"                              \
        "fcdotpex.s.h  %[sum00], %[a01], %[b10];"                              \
        "fcdotpex.s.h  %[sum10], %[a11], %[b10];"                              \
        "fcdotpex.s.h  %[sum01], %[a01], %[b11];"                              \
        "fcdotpex.s.h  %[sum11], %[a11], %[b11];"                              \
        "fcdotpex.s.h  %[sum02], %[a01], %[b12];"                              \
        "fcdotpex.s.h  %[sum12], %[a11], %[b12];"                              \
        "fcdotpex.s.h  %[sum03], %[a01], %[b13];"                              \
        "fcdotpex.s.h  %[sum13], %[a11], %[b13];"                              \
        : [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum02] "+&r"(sum02),    \
          [sum03] "+&r"(sum03), [sum10] "+&r"(sum10), [sum11] "+&r"(sum11),    \
          [sum12] "+&r"(sum12), [sum13] "+&r"(sum13)                           \
        : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),      \
          [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),      \
          [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13)       \
        :);                                                                    \
  }                                                                            \
  C[i * P + k + 0] = sum00;                                                    \
  C[i * P + k + 1] = sum01;                                                    \
  C[i * P + k + 2] = sum02;                                                    \
  C[i * P + k + 3] = sum03;                                                    \
  C[(i + 1) * P + k + 0] = sum10;                                              \
  C[(i + 1) * P + k + 1] = sum11;                                              \
  C[(i + 1) * P + k + 2] = sum12;                                              \
  C[(i + 1) * P + k + 3] = sum13;

#define __CDOTP
void cmatmul_2x2_f16s(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = 0; k < P; k += 2) {
    for (i = 0; i < M; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x2_LOOP;
#else
      CMATMUL_2x2_LOOP;
#endif
    }
  }
  return;
}

void cmatmul_2x2_f16p(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t core_id,
                      uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = core_id * 2; k < P; k += 2 * numThreads) {
    for (i = 0; i < M; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x2_LOOP;
#else
      CMATMUL_2x2_LOOP;
#endif
    }
  }
  mempool_log_partial_barrier(2, core_id, numThreads);
  return;
}

#define __SHIFT_A
void cmatmul_2x4_f16p(v2h *__restrict__ A, v2h const *__restrict__ B,
                      v2h *__restrict__ C, uint32_t M, uint32_t N, uint32_t P,
                      uint32_t core_id, uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
#ifndef __SHIFT_A
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = 0; i < M; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x4_LOOP;
#else
      CMATMUL_2x4_LOOP;
#endif
    }
  }
#else
  uint32_t shift_id = 2 * (core_id % NUM_CORES_PER_TILE);
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = shift_id; i < M; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x4_LOOP;
#else
      CMATMUL_2x4_LOOP;
#endif
    }
    for (i = 0; i < shift_id; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x4_LOOP;
#else
      CMATMUL_2x4_LOOP;
#endif
    }
  }
#endif
  mempool_log_partial_barrier(2, core_id, numThreads);
  return;
}

void cmatmul_2x4_folded_f16p(v2h *A, v2h const *__restrict__ B,
                             v2h *__restrict__ A_folded, v2h *__restrict__ C,
                             uint32_t M, uint32_t N, uint32_t P,
                             uint32_t core_id, uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  // Copy multiple A matrices in memory
  uint32_t num_copy = NUM_BANKS / (N * M);
  for (k = core_id * 4; k < N * M; k += 4 * numThreads) {
    v2h a0 = A[k];
    v2h a1 = A[k + 1];
    v2h a2 = A[k + 2];
    v2h a3 = A[k + 3];
    i = k / N; // row_index
    j = k % N; // col_index
    for (uint32_t idx_copy = 0; idx_copy < num_copy; idx_copy++) {
      A_folded[idx_copy * N * M + i * N + j] = a0;
      A_folded[idx_copy * N * M + i * N + j + 1] = a1;
      A_folded[idx_copy * N * M + i * N + j + 2] = a2;
      A_folded[idx_copy * N * M + i * N + j + 3] = a3;
    }
  }
  A = A_folded + (N * M) * ((core_id * BANKING_FACTOR) / (N * M));
  mempool_log_partial_barrier(2, core_id, numThreads);
  // Compute
#ifndef __SHIFT_A
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = 0; i < M; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x4_LOOP;
#else
      CMATMUL_2x4_LOOP;
#endif
    }
  }
#else
  uint32_t shift_id = 2 * (core_id % NUM_CORES_PER_TILE);
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = shift_id; i < M; i += 2) {
      // CMATMUL_2x4_LOOP;
      CMATMUL_CDOTP_2x4_LOOP;
    }
    for (i = 0; i < shift_id; i += 2) {
#ifdef __CDOTP
      CMATMUL_CDOTP_2x4_LOOP;
#else
      CMATMUL_2x4_LOOP;
#endif
    }
  }
#endif
  mempool_log_partial_barrier(2, core_id, numThreads);
  return;
}
