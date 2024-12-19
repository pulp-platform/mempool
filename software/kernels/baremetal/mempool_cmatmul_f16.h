// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

/* This library implements the complex matrix multiplication in
 * different ways. The functions all follow this format:
 *
 * A is an M x N matrix, B is a N x P matrix, and C is a M x P matrix
 * C = AB
 */

#pragma once
#include "builtins_v2.h"
#define __CDOTP   // Use complex dotp in a single offload
#define __SHIFT_A // Shift cores startpoint over rows of matrix A

/******************************************************************************
 __        ___     _            _                   ____        _
 \ \      / (_) __| | ___ _ __ (_)_ __   __ _      |  _ \  ___ | |_ _ __
  \ \ /\ / /| |/ _` |/ _ \ '_ \| | '_ \ / _` |_____| | | |/ _ \| __| '_ \
   \ V  V / | | (_| |  __/ | | | | | | | (_| |_____| |_| | (_) | |_| |_) |
    \_/\_/  |_|\__,_|\___|_| |_|_|_| |_|\__, |     |____/ \___/ \__| .__/
                                        |___/                      |_|

******************************************************************************/

#ifndef __CDOTP

#define CMATMUL_2x2_LOOP                                                       \
  {                                                                            \
    float sum00_real = 0.0f;                                                   \
    float sum01_real = 0.0f;                                                   \
    float sum10_real = 0.0f;                                                   \
    float sum11_real = 0.0f;                                                   \
    float sum00_imag = 0.0f;                                                   \
    float sum01_imag = 0.0f;                                                   \
    float sum10_imag = 0.0f;                                                   \
    float sum11_imag = 0.0f;                                                   \
    v2h a00s, a01s, a10s, a11s;                                                \
    v2h res00, res01, res10, res11;                                            \
    for (j = 0; j < N; j += 2) {                                               \
      v2h a00 = *(v2h *)&A[2 * ((i + 0) * N + (j + 0))];                       \
      v2h a01 = *(v2h *)&A[2 * ((i + 0) * N + (j + 1))];                       \
      v2h a10 = *(v2h *)&A[2 * ((i + 1) * N + (j + 0))];                       \
      v2h a11 = *(v2h *)&A[2 * ((i + 1) * N + (j + 1))];                       \
      v2h b00 = *(v2h *)&B[2 * ((j + 0) * P + (k + 0))];                       \
      v2h b01 = *(v2h *)&B[2 * ((j + 0) * P + (k + 1))];                       \
      v2h b10 = *(v2h *)&B[2 * ((j + 1) * P + (k + 0))];                       \
      v2h b11 = *(v2h *)&B[2 * ((j + 1) * P + (k + 1))];                       \
      asm volatile("pv.shuffle2.h  %[a00s], %[a00], %[mask];"                  \
                   "pv.shuffle2.h  %[a10s], %[a10], %[mask];"                  \
                   "pv.shuffle2.h  %[a01s], %[a01], %[mask];"                  \
                   "pv.shuffle2.h  %[a11s], %[a11], %[mask];"                  \
                   : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s),                   \
                     [a10s] "=&r"(a10s), [a11s] "=&r"(a11s)                    \
                   : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),           \
                     [a11] "r"(a11), [mask] "r"(0x00020003)                    \
                   :);                                                         \
      asm volatile(                                                            \
          "vfdotpex.s.h  %[sum00_imag], %[a00s], %[b00];"                      \
          "vfdotpex.s.h  %[sum10_imag], %[a10s], %[b00];"                      \
          "vfdotpex.s.h  %[sum01_imag], %[a00s], %[b01];"                      \
          "vfdotpex.s.h  %[sum11_imag], %[a10s], %[b01];"                      \
          "vfdotpex.s.h  %[sum00_imag], %[a01s], %[b10];"                      \
          "vfdotpex.s.h  %[sum10_imag], %[a11s], %[b10];"                      \
          "vfdotpex.s.h  %[sum01_imag], %[a01s], %[b11];"                      \
          "vfdotpex.s.h  %[sum11_imag], %[a11s], %[b11];"                      \
          : [sum00_imag] "+&r"(sum00_imag), [sum01_imag] "+&r"(sum01_imag),    \
            [sum10_imag] "+&r"(sum10_imag), [sum11_imag] "+&r"(sum11_imag)     \
          : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),              \
            [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10),  \
            [b11] "r"(b11)                                                     \
          :);                                                                  \
      asm volatile("xor  %[a00s], %[a00], %[mask];"                            \
                   "xor  %[a10s], %[a10], %[mask];"                            \
                   "xor  %[a01s], %[a01], %[mask];"                            \
                   "xor  %[a11s], %[a11], %[mask];"                            \
                   : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s),                   \
                     [a10s] "=&r"(a10s), [a11s] "=&r"(a11s)                    \
                   : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10),           \
                     [a11] "r"(a11), [mask] "r"(0x00008000)                    \
                   :);                                                         \
      asm volatile(                                                            \
          "vfdotpex.s.h  %[sum00_real], %[a00s], %[b00];"                      \
          "vfdotpex.s.h  %[sum10_real], %[a10s], %[b00];"                      \
          "vfdotpex.s.h  %[sum01_real], %[a00s], %[b01];"                      \
          "vfdotpex.s.h  %[sum11_real], %[a10s], %[b01];"                      \
          "vfdotpex.s.h  %[sum00_real], %[a01s], %[b10];"                      \
          "vfdotpex.s.h  %[sum10_real], %[a11s], %[b10];"                      \
          "vfdotpex.s.h  %[sum01_real], %[a01s], %[b11];"                      \
          "vfdotpex.s.h  %[sum11_real], %[a11s], %[b11];"                      \
          : [sum00_real] "+&r"(sum00_real), [sum01_real] "+&r"(sum01_real),    \
            [sum10_real] "+&r"(sum10_real), [sum11_real] "+&r"(sum11_real)     \
          : [a00s] "r"(a00s), [a01s] "r"(a01s), [a10s] "r"(a10s),              \
            [a11s] "r"(a11s), [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10),  \
            [b11] "r"(b11)                                                     \
          :);                                                                  \
    }                                                                          \
    asm volatile("vfcpka.h.s %[res00], %[sum00_imag], %[sum00_real];"          \
                 "vfcpka.h.s %[res01], %[sum01_imag], %[sum01_real];"          \
                 "vfcpka.h.s %[res10], %[sum10_imag], %[sum10_real];"          \
                 "vfcpka.h.s %[res11], %[sum11_imag], %[sum11_real];"          \
                 : [res00] "=r"(res00), [res01] "=r"(res01),                   \
                   [res10] "=r"(res10), [res11] "=r"(res11)                    \
                 : [sum00_imag] "r"(sum00_imag), [sum01_imag] "r"(sum01_imag), \
                   [sum10_imag] "r"(sum10_imag), [sum11_imag] "r"(sum11_imag), \
                   [sum00_real] "r"(sum00_real), [sum01_real] "r"(sum01_real), \
                   [sum10_real] "r"(sum10_real), [sum11_real] "r"(sum11_real)  \
                 :);                                                           \
    (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = res00;                           \
    (*(v2h *)&C[2 * ((i + 0) * P + k + 1)]) = res01;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = res10;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = res11;                           \
  }

#define CMATMUL_2x4_LOOP                                                       \
  {                                                                            \
    float sum00_real = 0.0f;                                                   \
    float sum01_real = 0.0f;                                                   \
    float sum02_real = 0.0f;                                                   \
    float sum03_real = 0.0f;                                                   \
    float sum10_real = 0.0f;                                                   \
    float sum11_real = 0.0f;                                                   \
    float sum12_real = 0.0f;                                                   \
    float sum13_real = 0.0f;                                                   \
    float sum00_imag = 0.0f;                                                   \
    float sum01_imag = 0.0f;                                                   \
    float sum02_imag = 0.0f;                                                   \
    float sum03_imag = 0.0f;                                                   \
    float sum10_imag = 0.0f;                                                   \
    float sum11_imag = 0.0f;                                                   \
    float sum12_imag = 0.0f;                                                   \
    float sum13_imag = 0.0f;                                                   \
    v2h a00s, a01s, a10s, a11s;                                                \
    for (j = 0; j < N; j += 2) {                                               \
      v2h a00 = A[(i + 0) * N + (j + 0)];                                      \
      v2h a01 = A[(i + 0) * N + (j + 1)];                                      \
      v2h a10 = A[(i + 1) * N + (j + 0)];                                      \
      v2h a11 = A[(i + 1) * N + (j + 1)];                                      \
      v2h b00 = B[(j + 0) * P + (k + 0)];                                      \
      v2h b01 = B[(j + 0) * P + (k + 1)];                                      \
      v2h b02 = B[(j + 0) * P + (k + 2)];                                      \
      v2h b03 = B[(j + 0) * P + (k + 3)];                                      \
      v2h b10 = B[(j + 1) * P + (k + 0)];                                      \
      v2h b11 = B[(j + 1) * P + (k + 1)];                                      \
      v2h b12 = B[(j + 1) * P + (k + 2)];                                      \
      v2h b13 = B[(j + 1) * P + (k + 3)];                                      \
      asm volatile(                                                            \
          "pv.shuffle2.h  %[a00s], %[a00], %[mask];"                           \
          "pv.shuffle2.h  %[a10s], %[a10], %[mask];"                           \
          "pv.shuffle2.h  %[a01s], %[a01], %[mask];"                           \
          "pv.shuffle2.h  %[a11s], %[a11], %[mask];"                           \
          "vfdotpex.s.h  %[sum00_imag], %[a00s], %[b00];"                      \
          "vfdotpex.s.h  %[sum10_imag], %[a10s], %[b00];"                      \
          "vfdotpex.s.h  %[sum01_imag], %[a00s], %[b01];"                      \
          "vfdotpex.s.h  %[sum11_imag], %[a10s], %[b01];"                      \
          "vfdotpex.s.h  %[sum02_imag], %[a00s], %[b02];"                      \
          "vfdotpex.s.h  %[sum12_imag], %[a10s], %[b02];"                      \
          "vfdotpex.s.h  %[sum03_imag], %[a00s], %[b03];"                      \
          "vfdotpex.s.h  %[sum13_imag], %[a10s], %[b03];"                      \
          "vfdotpex.s.h  %[sum00_imag], %[a01s], %[b10];"                      \
          "vfdotpex.s.h  %[sum10_imag], %[a11s], %[b10];"                      \
          "vfdotpex.s.h  %[sum01_imag], %[a01s], %[b11];"                      \
          "vfdotpex.s.h  %[sum11_imag], %[a11s], %[b11];"                      \
          "vfdotpex.s.h  %[sum02_imag], %[a01s], %[b12];"                      \
          "vfdotpex.s.h  %[sum12_imag], %[a11s], %[b12];"                      \
          "vfdotpex.s.h  %[sum03_imag], %[a01s], %[b13];"                      \
          "vfdotpex.s.h  %[sum13_imag], %[a11s], %[b13];"                      \
          : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s),        \
            [a11s] "=&r"(a11s), [sum00_imag] "+&r"(sum00_imag),                \
            [sum01_imag] "+&r"(sum01_imag), [sum02_imag] "+&r"(sum02_imag),    \
            [sum03_imag] "+&r"(sum03_imag), [sum10_imag] "+&r"(sum10_imag),    \
            [sum11_imag] "+&r"(sum11_imag), [sum12_imag] "+&r"(sum12_imag),    \
            [sum13_imag] "+&r"(sum13_imag)                                     \
          : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),    \
            [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),    \
            [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13),    \
            [mask] "r"(0x00020003)                                             \
          :);                                                                  \
      asm volatile(                                                            \
          "xor  %[a00s], %[a00], %[maskn];"                                    \
          "xor  %[a10s], %[a10], %[maskn];"                                    \
          "xor  %[a01s], %[a01], %[maskn];"                                    \
          "xor  %[a11s], %[a11], %[maskn];"                                    \
          "vfdotpex.s.h  %[sum00_real], %[a00s], %[b00];"                      \
          "vfdotpex.s.h  %[sum10_real], %[a10s], %[b00];"                      \
          "vfdotpex.s.h  %[sum01_real], %[a00s], %[b01];"                      \
          "vfdotpex.s.h  %[sum11_real], %[a10s], %[b01];"                      \
          "vfdotpex.s.h  %[sum02_real], %[a00s], %[b02];"                      \
          "vfdotpex.s.h  %[sum12_real], %[a10s], %[b02];"                      \
          "vfdotpex.s.h  %[sum03_real], %[a00s], %[b03];"                      \
          "vfdotpex.s.h  %[sum13_real], %[a10s], %[b03];"                      \
          "vfdotpex.s.h  %[sum00_real], %[a01s], %[b10];"                      \
          "vfdotpex.s.h  %[sum10_real], %[a11s], %[b10];"                      \
          "vfdotpex.s.h  %[sum01_real], %[a01s], %[b11];"                      \
          "vfdotpex.s.h  %[sum11_real], %[a11s], %[b11];"                      \
          "vfdotpex.s.h  %[sum02_real], %[a01s], %[b12];"                      \
          "vfdotpex.s.h  %[sum12_real], %[a11s], %[b12];"                      \
          "vfdotpex.s.h  %[sum03_real], %[a01s], %[b13];"                      \
          "vfdotpex.s.h  %[sum13_real], %[a11s], %[b13];"                      \
          : [a00s] "=&r"(a00s), [a01s] "=&r"(a01s), [a10s] "=&r"(a10s),        \
            [a11s] "=&r"(a11s), [sum00_real] "+&r"(sum00_real),                \
            [sum01_real] "+&r"(sum01_real), [sum02_real] "+&r"(sum02_real),    \
            [sum03_real] "+&r"(sum03_real), [sum10_real] "+&r"(sum10_real),    \
            [sum11_real] "+&r"(sum11_real), [sum12_real] "+&r"(sum12_real),    \
            [sum13_real] "+&r"(sum13_real)                                     \
          : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),    \
            [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),    \
            [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13),    \
            [maskn] "r"(0x00008000)                                            \
          :);                                                                  \
    }                                                                          \
    asm volatile(                                                              \
        "vfcpka.h.s %[sum00_real], %[sum00_imag], %[sum00_real];"              \
        "vfcpka.h.s %[sum01_real], %[sum01_imag], %[sum01_real];"              \
        "vfcpka.h.s %[sum02_real], %[sum02_imag], %[sum02_real];"              \
        "vfcpka.h.s %[sum03_real], %[sum03_imag], %[sum03_real];"              \
        "vfcpka.h.s %[sum10_real], %[sum10_imag], %[sum10_real];"              \
        "vfcpka.h.s %[sum11_real], %[sum11_imag], %[sum11_real];"              \
        "vfcpka.h.s %[sum12_real], %[sum12_imag], %[sum12_real];"              \
        "vfcpka.h.s %[sum13_real], %[sum13_imag], %[sum13_real];"              \
        : [sum00_real] "+&r"(sum00_real), [sum01_real] "+&r"(sum01_real),      \
          [sum02_real] "+&r"(sum02_real), [sum03_real] "+&r"(sum03_real),      \
          [sum10_real] "+&r"(sum10_real), [sum11_real] "+&r"(sum11_real),      \
          [sum12_real] "+&r"(sum12_real), [sum13_real] "+&r"(sum13_real)       \
        : [sum00_imag] "r"(sum00_imag), [sum01_imag] "r"(sum01_imag),          \
          [sum02_imag] "r"(sum02_imag), [sum03_imag] "r"(sum03_imag),          \
          [sum10_imag] "r"(sum10_imag), [sum11_imag] "r"(sum11_imag),          \
          [sum12_imag] "r"(sum12_imag), [sum13_imag] "r"(sum13_imag)           \
        :);                                                                    \
    C[(i + 0) * P + k + 0] = (v2h)sum00_real;                                  \
    C[(i + 0) * P + k + 1] = (v2h)sum01_real;                                  \
    C[(i + 0) * P + k + 2] = (v2h)sum02_real;                                  \
    C[(i + 0) * P + k + 3] = (v2h)sum03_real;                                  \
    C[(i + 1) * P + k + 0] = (v2h)sum10_real;                                  \
    C[(i + 1) * P + k + 1] = (v2h)sum11_real;                                  \
    C[(i + 1) * P + k + 2] = (v2h)sum12_real;                                  \
    C[(i + 1) * P + k + 3] = (v2h)sum13_real;                                  \
  }

#endif

/******************************************************************************
   ____                      _                ____        _
  / ___|___  _ __ ___  _ __ | | _____  __    |  _ \  ___ | |_ _ __
 | |   / _ \| '_ ` _ \| '_ \| |/ _ \ \/ /____| | | |/ _ \| __| '_ \
 | |__| (_) | | | | | | |_) | |  __/>  <_____| |_| | (_) | |_| |_) |
  \____\___/|_| |_| |_| .__/|_|\___/_/\_\    |____/ \___/ \__| .__/
                      |_|                                    |_|

******************************************************************************/

#ifdef __CDOTP

#define CMATMUL_2x2_LOOP                                                       \
  {                                                                            \
    v2h sum00 = (v2h)0.0f;                                                     \
    v2h sum01 = (v2h)0.0f;                                                     \
    v2h sum10 = (v2h)0.0f;                                                     \
    v2h sum11 = (v2h)0.0f;                                                     \
    for (j = 0; j < N; j += 2) {                                               \
      v2h a00 = *(v2h *)&A[2 * ((i + 0) * M + (j + 0))];                       \
      v2h a01 = *(v2h *)&A[2 * ((i + 0) * M + (j + 1))];                       \
      v2h a10 = *(v2h *)&A[2 * ((i + 1) * M + (j + 0))];                       \
      v2h a11 = *(v2h *)&A[2 * ((i + 1) * M + (j + 1))];                       \
      v2h b00 = *(v2h *)&B[2 * ((j + 0) * P + (k + 0))];                       \
      v2h b01 = *(v2h *)&B[2 * ((j + 0) * P + (k + 1))];                       \
      v2h b10 = *(v2h *)&B[2 * ((j + 1) * P + (k + 0))];                       \
      v2h b11 = *(v2h *)&B[2 * ((j + 1) * P + (k + 1))];                       \
      asm volatile(                                                            \
          "fcdotpex.s.h  %[sum00], %[a00], %[b00];"                            \
          "fcdotpex.s.h  %[sum10], %[a10], %[b00];"                            \
          "fcdotpex.s.h  %[sum01], %[a00], %[b01];"                            \
          "fcdotpex.s.h  %[sum11], %[a10], %[b01];"                            \
          "fcdotpex.s.h  %[sum00], %[a01], %[b10];"                            \
          "fcdotpex.s.h  %[sum10], %[a11], %[b10];"                            \
          "fcdotpex.s.h  %[sum01], %[a01], %[b11];"                            \
          "fcdotpex.s.h  %[sum11], %[a11], %[b11];"                            \
          : [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum10] "+&r"(sum10),  \
            [sum11] "+&r"(sum11)                                               \
          : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),    \
            [b00] "r"(b00), [b01] "r"(b01), [b10] "r"(b10), [b11] "r"(b11)     \
          :);                                                                  \
    }                                                                          \
    (*(v2h *)&C[2 * ((i + 0) * P + k + 0)]) = sum00;                           \
    (*(v2h *)&C[2 * ((i + 0) * P + k + 1)]) = sum01;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = sum10;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = sum11;                           \
  }

#define CMATMUL_2x4_LOOP                                                       \
  {                                                                            \
    v2h sum00 = (v2h)0.0f;                                                     \
    v2h sum01 = (v2h)0.0f;                                                     \
    v2h sum02 = (v2h)0.0f;                                                     \
    v2h sum03 = (v2h)0.0f;                                                     \
    v2h sum10 = (v2h)0.0f;                                                     \
    v2h sum11 = (v2h)0.0f;                                                     \
    v2h sum12 = (v2h)0.0f;                                                     \
    v2h sum13 = (v2h)0.0f;                                                     \
    for (j = 0; j < N; j += 2) {                                               \
      v2h a00 = *(v2h *)&A[2 * (i * M + j + 0)];                               \
      v2h a01 = *(v2h *)&A[2 * (i * M + j + 1)];                               \
      v2h a10 = *(v2h *)&A[2 * ((i + 1) * M + j + 0)];                         \
      v2h a11 = *(v2h *)&A[2 * ((i + 1) * M + j + 1)];                         \
      v2h b00 = *(v2h *)&B[2 * (j * P + k + 0)];                               \
      v2h b01 = *(v2h *)&B[2 * (j * P + k + 1)];                               \
      v2h b02 = *(v2h *)&B[2 * (j * P + k + 2)];                               \
      v2h b03 = *(v2h *)&B[2 * (j * P + k + 3)];                               \
      v2h b10 = *(v2h *)&B[2 * ((j + 1) * P + k + 0)];                         \
      v2h b11 = *(v2h *)&B[2 * ((j + 1) * P + k + 1)];                         \
      v2h b12 = *(v2h *)&B[2 * ((j + 1) * P + k + 2)];                         \
      v2h b13 = *(v2h *)&B[2 * ((j + 1) * P + k + 3)];                         \
      asm volatile(                                                            \
          "fcdotpex.s.h  %[sum00], %[a00], %[b00];"                            \
          "fcdotpex.s.h  %[sum10], %[a10], %[b00];"                            \
          "fcdotpex.s.h  %[sum01], %[a00], %[b01];"                            \
          "fcdotpex.s.h  %[sum11], %[a10], %[b01];"                            \
          "fcdotpex.s.h  %[sum02], %[a00], %[b02];"                            \
          "fcdotpex.s.h  %[sum12], %[a10], %[b02];"                            \
          "fcdotpex.s.h  %[sum03], %[a00], %[b03];"                            \
          "fcdotpex.s.h  %[sum13], %[a10], %[b03];"                            \
          "fcdotpex.s.h  %[sum00], %[a01], %[b10];"                            \
          "fcdotpex.s.h  %[sum10], %[a11], %[b10];"                            \
          "fcdotpex.s.h  %[sum01], %[a01], %[b11];"                            \
          "fcdotpex.s.h  %[sum11], %[a11], %[b11];"                            \
          "fcdotpex.s.h  %[sum02], %[a01], %[b12];"                            \
          "fcdotpex.s.h  %[sum12], %[a11], %[b12];"                            \
          "fcdotpex.s.h  %[sum03], %[a01], %[b13];"                            \
          "fcdotpex.s.h  %[sum13], %[a11], %[b13];"                            \
          : [sum00] "+&r"(sum00), [sum01] "+&r"(sum01), [sum02] "+&r"(sum02),  \
            [sum03] "+&r"(sum03), [sum10] "+&r"(sum10), [sum11] "+&r"(sum11),  \
            [sum12] "+&r"(sum12), [sum13] "+&r"(sum13)                         \
          : [a00] "r"(a00), [a01] "r"(a01), [a10] "r"(a10), [a11] "r"(a11),    \
            [b00] "r"(b00), [b01] "r"(b01), [b02] "r"(b02), [b03] "r"(b03),    \
            [b10] "r"(b10), [b11] "r"(b11), [b12] "r"(b12), [b13] "r"(b13)     \
          :);                                                                  \
    }                                                                          \
    (*(v2h *)&C[2 * (i * P + k + 0)]) = sum00;                                 \
    (*(v2h *)&C[2 * (i * P + k + 1)]) = sum01;                                 \
    (*(v2h *)&C[2 * (i * P + k + 2)]) = sum02;                                 \
    (*(v2h *)&C[2 * (i * P + k + 3)]) = sum03;                                 \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 0)]) = sum10;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 1)]) = sum11;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 2)]) = sum12;                           \
    (*(v2h *)&C[2 * ((i + 1) * P + k + 3)]) = sum13;                           \
  }

#define CMATMUL_4x4_LOOP                                                       \
  {                                                                            \
    __fp16 const *addr_a = &A[2 * i * N];                                      \
    __fp16 const *addr_b = &B[2 * j];                                          \
    __fp16 const *end_b = &B[2 * (N * P + j)];                                 \
    __fp16 const *addr_c = &C[2 * (i * P + j)];                                \
    int32_t const P3 = ((int32_t)P - 3) * 4;                                   \
    int32_t const N31 = (-3 * (int32_t)N + 1) * 4;                             \
    register int32_t k asm("x1") = (int32_t)end_b;                             \
    __asm__ volatile(                                                          \
        ".balign 16 \n\t"                                                      \
        "p.lw  x3, %[N](%[addr_a]!) \n\t"                                      \
        "p.lw x12, 4(%[addr_b]!) \n\t"                                         \
        "p.lw x13, 4(%[addr_b]!) \n\t"                                         \
        "p.lw x14, 4(%[addr_b]!) \n\t"                                         \
        "p.lw x15, %[P3](%[addr_b]!) \n\t"                                     \
        "p.lw  x4, %[N](%[addr_a]!) \n\t"                                      \
        "p.lw x10, %[N](%[addr_a]!) \n\t"                                      \
        "p.lw x11, %[N31](%[addr_a]!) \n\t"                                    \
        "mv x16, zero \n\t"                                                    \
        "mv x17, zero \n\t"                                                    \
        "mv x18, zero \n\t"                                                    \
        "mv x19, zero \n\t"                                                    \
        "mv x20, zero \n\t"                                                    \
        "mv x21, zero \n\t"                                                    \
        "mv x22, zero \n\t"                                                    \
        "mv x23, zero \n\t"                                                    \
        "mv x24, zero \n\t"                                                    \
        "mv x25, zero \n\t"                                                    \
        "mv x26, zero \n\t"                                                    \
        "mv x27, zero \n\t"                                                    \
        "mv x28, zero \n\t"                                                    \
        "mv x29, zero \n\t"                                                    \
        "mv x30, zero \n\t"                                                    \
        "mv x31, zero \n\t"                                                    \
        "fcdotpex.s.h x16,  x3, x12 \n\t"                                      \
        "fcdotpex.s.h x17,  x3, x13 \n\t"                                      \
        "fcdotpex.s.h x18,  x3, x14 \n\t"                                      \
        "fcdotpex.s.h x19,  x3, x15 \n\t"                                      \
        "p.lw  x3, %[N](%[addr_a]!) \n\t"                                      \
        "fcdotpex.s.h x20,  x4, x12 \n\t"                                      \
        "fcdotpex.s.h x21,  x4, x13 \n\t"                                      \
        "fcdotpex.s.h x22,  x4, x14 \n\t"                                      \
        "fcdotpex.s.h x23,  x4, x15 \n\t"                                      \
        "p.lw  x4, %[N](%[addr_a]!) \n\t"                                      \
        "fcdotpex.s.h x24, x10, x12 \n\t"                                      \
        "fcdotpex.s.h x25, x10, x13 \n\t"                                      \
        "fcdotpex.s.h x26, x10, x14 \n\t"                                      \
        "fcdotpex.s.h x27, x10, x15 \n\t"                                      \
        "p.lw x10, %[N](%[addr_a]!) \n\t"                                      \
        "fcdotpex.s.h x28, x11, x12 \n\t"                                      \
        "p.lw x12, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x29, x11, x13 \n\t"                                      \
        "p.lw x13, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x30, x11, x14 \n\t"                                      \
        "p.lw x14, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x31, x11, x15 \n\t"                                      \
        "p.lw x15, %[P3](%[addr_b]!) \n\t"                                     \
        "p.lw x11, %[N31](%[addr_a]!) \n\t"                                    \
        "1: \n\t"                                                              \
        "fcdotpex.s.h x16,  x3, x12 \n\t"                                      \
        "fcdotpex.s.h x17,  x3, x13 \n\t"                                      \
        "fcdotpex.s.h x20,  x4, x12 \n\t"                                      \
        "fcdotpex.s.h x21,  x4, x13 \n\t"                                      \
        "fcdotpex.s.h x18,  x3, x14 \n\t"                                      \
        "fcdotpex.s.h x22,  x4, x14 \n\t"                                      \
        "fcdotpex.s.h x19,  x3, x15 \n\t"                                      \
        "p.lw  x3, %[N](%[addr_a]!) \n\t"                                      \
        "fcdotpex.s.h x23,  x4, x15 \n\t"                                      \
        "p.lw  x4, %[N](%[addr_a]!) \n\t"                                      \
        "fcdotpex.s.h x24, x10, x12 \n\t"                                      \
        "fcdotpex.s.h x28, x11, x12 \n\t"                                      \
        "p.lw x12, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x25, x10, x13 \n\t"                                      \
        "fcdotpex.s.h x29, x11, x13 \n\t"                                      \
        "p.lw x13, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x26, x10, x14 \n\t"                                      \
        "fcdotpex.s.h x30, x11, x14 \n\t"                                      \
        "p.lw x14, 4(%[addr_b]!) \n\t"                                         \
        "fcdotpex.s.h x27, x10, x15 \n\t"                                      \
        "fcdotpex.s.h x31, x11, x15 \n\t"                                      \
        "p.lw x15, %[P3](%[addr_b]!) \n\t"                                     \
        "p.lw x10, %[N](%[addr_a]!) \n\t"                                      \
        "p.lw x11, %[N31](%[addr_a]!) \n\t"                                    \
        "bne %[addr_b], x1, 1b \n\t"                                           \
        "fcdotpex.s.h x16,  x3, x12 \n\t"                                      \
        "fcdotpex.s.h x17,  x3, x13 \n\t"                                      \
        "fcdotpex.s.h x18,  x3, x14 \n\t"                                      \
        "p.sw x16, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x19,  x3, x15 \n\t"                                      \
        "p.sw x17, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x20,  x4, x12 \n\t"                                      \
        "p.sw x18, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x21,  x4, x13 \n\t"                                      \
        "p.sw x19, %[P3](%[addr_c]!) \n\t"                                     \
        "fcdotpex.s.h x22,  x4, x14 \n\t"                                      \
        "p.sw x20, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x23,  x4, x15 \n\t"                                      \
        "p.sw x21, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x24, x10, x12 \n\t"                                      \
        "p.sw x22, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x25, x10, x13 \n\t"                                      \
        "p.sw x23, %[P3](%[addr_c]!) \n\t"                                     \
        "fcdotpex.s.h x26, x10, x14 \n\t"                                      \
        "p.sw x24, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x27, x10, x15 \n\t"                                      \
        "p.sw x25, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x28, x11, x12 \n\t"                                      \
        "p.sw x26, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x29, x11, x13 \n\t"                                      \
        "p.sw x27, %[P3](%[addr_c]!) \n\t"                                     \
        "fcdotpex.s.h x30, x11, x14 \n\t"                                      \
        "p.sw x28, 4(%[addr_c]!) \n\t"                                         \
        "fcdotpex.s.h x31, x11, x15 \n\t"                                      \
        "p.sw x29, 4(%[addr_c]!) \n\t"                                         \
        "p.sw x30, 4(%[addr_c]!) \n\t"                                         \
        "p.sw x31, %[P3](%[addr_c]!) \n\t"                                     \
        :                                                                      \
        [addr_a] "+&r"(addr_a), [addr_b] "+&r"(addr_b), [addr_c] "+&r"(addr_c) \
        : [N31] "r"(N31), [P3] "r"(P3), [x1] "r"(k), [N] "I"(dim_N * 4)        \
        : "x3", "x4", "x10", "x11", "x12", "x13", "x14", "x15", "x16", "x17",  \
          "x18", "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26",       \
          "x27", "x28", "x29", "x30", "x31", "memory");                        \
  }

#endif

// 2x2 MATMUL
void cmatmul_2x2_f16s(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = 0; k < P; k += 2) {
    for (i = 0; i < M; i += 2) {
      CMATMUL_2x2_LOOP;
    }
  }
  return;
}

// 2x2 MATMUL
void cmatmul_2x2_f16p(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t core_id,
                      uint32_t numThreads) {

  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
  for (k = core_id * 2; k < P; k += 2 * numThreads) {
    for (i = 0; i < M; i += 2) {
      CMATMUL_2x2_LOOP;
    }
  }
  return;
}

// 2x4 MATMUL
void cmatmul_2x4_f16p(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t core_id,
                      uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P
#ifndef __SHIFT_A
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = 0; i < M; i += 2) {
      CMATMUL_2x4_LOOP;
    }
  }
#else
  uint32_t shift_id = (2 * (core_id % NUM_CORES_PER_TILE)) % M;
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = shift_id; i < M; i += 2) {
      CMATMUL_2x4_LOOP;
    }
    for (i = 0; i < shift_id; i += 2) {
      CMATMUL_2x4_LOOP;
    }
  }
#endif
  return;
}

#ifdef __CDOTP

// 4x4 MATMUL
void cmatmul_4x4_f16p(__fp16 const *__restrict__ A,
                      __fp16 const *__restrict__ B, __fp16 *__restrict__ C,
                      uint32_t M, uint32_t N, uint32_t P, uint32_t core_id,
                      uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t shift_id = (4 * (core_id % NUM_CORES_PER_TILE)) % M;
  for (j = 4 * core_id; j < P; j += 4 * numThreads) {
    for (i = shift_id; i < M; i += 4) {
      CMATMUL_4x4_LOOP
    }
    for (i = 0; i < shift_id; i += 4) {
      CMATMUL_4x4_LOOP
    }
  }
  return;
}

// 4x4 MATMUL with copies of A matrix (for M*N < NUM_BANKS)
void cmatmul_4x4_f16p_copy_A(__fp16 const *__restrict__ A_l2,
                             __fp16 *__restrict__ A_l1,
                             __fp16 const *__restrict__ B,
                             __fp16 *__restrict__ C, uint32_t M, uint32_t N,
                             uint32_t P, uint32_t core_id,
                             uint32_t numThreads) {

  // Copy multiple A matrices in memory
  if (core_id == 0) {
    for (uint32_t idx_copy = 0; idx_copy < (BANKING_FACTOR * NUM_CORES);
         idx_copy += 2 * (M * N)) {
      dma_memcpy_blocking(&A_l1[idx_copy], A_l2, M * N * sizeof(int32_t));
    }
  }
  // Cores only fetch from local A
  __fp16 *A_shifted = A_l1;
  A_shifted += (N * M) * ((core_id * BANKING_FACTOR) / (N * M));
  mempool_log_partial_barrier(2, core_id, numThreads);
  cmatmul_4x4_f16p(A_shifted, B, C, M, N, P, core_id, numThreads);
  return;
}

#endif
