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
#define __SHIFT_A // Shift cores startpoint over rows of matrix A

#define CMATMUL_1x1_LOOP                                                       \
  v2s sum = {0, 0};                                                            \
  for (j = 0; j < N; j++) {                                                    \
    v2s ab = *(v2s *)&A[2 * (i * N + j)];                                      \
    v2s cd = *(v2s *)&B[2 * (j * P + k)];                                      \
    int32_t re, im, temp;                                                      \
    asm volatile("pv.shuffle2.h %[temp],%[cd],%[mask_shuf];"                   \
                 "pv.dotsp.h    %[im],%[ab],%[temp];"                          \
                 "pv.sub.h      %[temp],zero,%[cd];"                           \
                 "srli          %[cd],%[cd],0x10;"                             \
                 "pv.pack       %[temp],%[cd],%[temp];"                        \
                 "pv.dotsp.h    %[re],%[ab],%[temp];"                          \
                 "srai          %[im],%[im],0x0F;"                             \
                 "srai          %[re],%[re],0x0F;"                             \
                 "pv.pack       %[re],%[re],%[im];"                            \
                 "pv.add.h      %[sum],%[sum],%[re];"                          \
                 : [re] "=&r"(re), [im] "=&r"(im), [temp] "=&r"(temp),         \
                   [cd] "+&r"(cd), [sum] "+&r"(sum)                            \
                 : [ab] "r"(ab), [mask_shuf] "r"(0x00020003)                   \
                 :);                                                           \
  }                                                                            \
  (*(v2s *)&C[2 * (i * P + k)]) = sum;

#define CMATMUL_2x2_LOOP                                                       \
  v2s sum00 = {0, 0};                                                          \
  v2s sum01 = {0, 0};                                                          \
  v2s sum10 = {0, 0};                                                          \
  v2s sum11 = {0, 0};                                                          \
  v2s temp00, temp01, temp10, temp11;                                          \
  int32_t re00, re01, re10, re11;                                              \
  int32_t im00, im01, im10, im11;                                              \
  for (j = 0; j < N; j += 2) {                                                 \
    v2s ab00 = *(v2s *)&A[2 * ((i + 0) * N + j + 0)];                          \
    v2s ab01 = *(v2s *)&A[2 * ((i + 0) * N + j + 1)];                          \
    v2s ab10 = *(v2s *)&A[2 * ((i + 1) * N + j + 0)];                          \
    v2s ab11 = *(v2s *)&A[2 * ((i + 1) * N + j + 1)];                          \
    v2s cd00 = *(v2s *)&B[2 * ((j + 0) * P + k + 0)];                          \
    v2s cd01 = *(v2s *)&B[2 * ((j + 0) * P + k + 1)];                          \
    v2s cd10 = *(v2s *)&B[2 * ((j + 1) * P + k + 0)];                          \
    v2s cd11 = *(v2s *)&B[2 * ((j + 1) * P + k + 1)];                          \
                                                                               \
    asm volatile("pv.shuffle2.h %[temp00],%[cd00],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp01],%[cd01],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp10],%[cd10],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp11],%[cd11],%[mask_shuf];"               \
                 : [temp00] "=&r"(temp00), [temp01] "=&r"(temp01),             \
                   [temp10] "=&r"(temp10), [temp11] "=&r"(temp11)              \
                 : [cd00] "r"(cd00), [cd01] "r"(cd01), [cd10] "r"(cd10),       \
                   [cd11] "r"(cd11), [mask_shuf] "r"(0x00020003)               \
                 :);                                                           \
    im00 = __DOTP2(ab00, temp00);                                              \
    im10 = __DOTP2(ab10, temp00);                                              \
    im01 = __DOTP2(ab00, temp01);                                              \
    im11 = __DOTP2(ab10, temp01);                                              \
    im00 = __SUMDOTP2(ab01, temp10, im00);                                     \
    im10 = __SUMDOTP2(ab11, temp10, im10);                                     \
    im01 = __SUMDOTP2(ab01, temp11, im01);                                     \
    im11 = __SUMDOTP2(ab11, temp11, im11);                                     \
    im00 = im00 >> 15;                                                         \
    im10 = im10 >> 15;                                                         \
    im01 = im01 >> 15;                                                         \
    im11 = im11 >> 15;                                                         \
                                                                               \
    temp00 = __EXOR2(cd00, (v2s)(0x0000FFFF));                                 \
    temp01 = __EXOR2(cd01, (v2s)(0x0000FFFF));                                 \
    temp10 = __EXOR2(cd10, (v2s)(0x0000FFFF));                                 \
    temp11 = __EXOR2(cd11, (v2s)(0x0000FFFF));                                 \
    temp00 = __ADD2(temp00, (v2s)(0x00000001));                                \
    temp01 = __ADD2(temp01, (v2s)(0x00000001));                                \
    temp10 = __ADD2(temp10, (v2s)(0x00000001));                                \
    temp11 = __ADD2(temp11, (v2s)(0x00000001));                                \
    re00 = __DOTP2(ab00, temp00);                                              \
    re10 = __DOTP2(ab10, temp00);                                              \
    re01 = __DOTP2(ab00, temp01);                                              \
    re11 = __DOTP2(ab10, temp01);                                              \
    re00 = __SUMDOTP2(ab01, temp10, re00);                                     \
    re10 = __SUMDOTP2(ab11, temp10, re10);                                     \
    re00 = re00 >> 15;                                                         \
    re10 = re10 >> 15;                                                         \
    v2s c00 = __PACK2(re00, im00);                                             \
    v2s c10 = __PACK2(re10, im10);                                             \
    sum00 = __ADD2(sum00, c00);                                                \
    sum10 = __ADD2(sum10, c10);                                                \
    re01 = __SUMDOTP2(ab01, temp11, re01);                                     \
    re11 = __SUMDOTP2(ab11, temp11, re11);                                     \
    re01 = re01 >> 15;                                                         \
    re11 = re11 >> 15;                                                         \
    v2s c01 = __PACK2(re01, im01);                                             \
    v2s c11 = __PACK2(re11, im11);                                             \
    sum01 = __ADD2(sum01, c01);                                                \
    sum11 = __ADD2(sum11, c11);                                                \
  }                                                                            \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 0)]) = sum00;                             \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 1)]) = sum01;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 0)]) = sum10;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 1)]) = sum11;

#define CMATMUL_2x4_LOOP                                                       \
  v2s sum00 = {0, 0};                                                          \
  v2s sum01 = {0, 0};                                                          \
  v2s sum02 = {0, 0};                                                          \
  v2s sum03 = {0, 0};                                                          \
  v2s sum10 = {0, 0};                                                          \
  v2s sum11 = {0, 0};                                                          \
  v2s sum12 = {0, 0};                                                          \
  v2s sum13 = {0, 0};                                                          \
  v2s temp00, temp01, temp10, temp11;                                          \
  int32_t re00, re01, re02, re03;                                              \
  int32_t re10, re11, re12, re13;                                              \
  int32_t im00, im01, im02, im03;                                              \
  int32_t im10, im11, im12, im13;                                              \
  for (j = 0; j < N; j += 2) {                                                 \
    v2s ab00 = *(v2s *)&A[2 * ((i + 0) * N + j + 0)];                          \
    v2s ab01 = *(v2s *)&A[2 * ((i + 0) * N + j + 1)];                          \
    v2s ab10 = *(v2s *)&A[2 * ((i + 1) * N + j + 0)];                          \
    v2s ab11 = *(v2s *)&A[2 * ((i + 1) * N + j + 1)];                          \
    v2s cd00 = *(v2s *)&B[2 * ((j + 0) * P + k + 0)];                          \
    v2s cd01 = *(v2s *)&B[2 * ((j + 0) * P + k + 1)];                          \
    v2s cd02 = *(v2s *)&B[2 * ((j + 0) * P + k + 2)];                          \
    v2s cd03 = *(v2s *)&B[2 * ((j + 0) * P + k + 3)];                          \
    v2s cd10 = *(v2s *)&B[2 * ((j + 1) * P + k + 0)];                          \
    v2s cd11 = *(v2s *)&B[2 * ((j + 1) * P + k + 1)];                          \
    v2s cd12 = *(v2s *)&B[2 * ((j + 1) * P + k + 2)];                          \
    v2s cd13 = *(v2s *)&B[2 * ((j + 1) * P + k + 3)];                          \
    asm volatile("pv.shuffle2.h %[temp00],%[ab00],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp01],%[ab01],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp10],%[ab10],%[mask_shuf];"               \
                 "pv.shuffle2.h %[temp11],%[ab11],%[mask_shuf];"               \
                 : [temp00] "=&r"(temp00), [temp01] "=&r"(temp01),             \
                   [temp10] "=&r"(temp10), [temp11] "=&r"(temp11)              \
                 : [ab00] "r"(ab00), [ab01] "r"(ab01), [ab10] "r"(ab10),       \
                   [ab11] "r"(ab11), [mask_shuf] "r"(0x00020003)               \
                 :);                                                           \
    im00 = __DOTP2(temp00, cd00);                                              \
    im01 = __DOTP2(temp00, cd01);                                              \
    im02 = __DOTP2(temp00, cd02);                                              \
    im03 = __DOTP2(temp00, cd03);                                              \
    im10 = __DOTP2(temp10, cd00);                                              \
    im11 = __DOTP2(temp10, cd01);                                              \
    im12 = __DOTP2(temp10, cd02);                                              \
    im13 = __DOTP2(temp10, cd03);                                              \
    im00 = __SUMDOTP2(temp01, cd10, im00);                                     \
    im01 = __SUMDOTP2(temp01, cd11, im01);                                     \
    im02 = __SUMDOTP2(temp01, cd12, im02);                                     \
    im03 = __SUMDOTP2(temp01, cd13, im03);                                     \
    im10 = __SUMDOTP2(temp11, cd10, im10);                                     \
    im11 = __SUMDOTP2(temp11, cd11, im11);                                     \
    im12 = __SUMDOTP2(temp11, cd12, im12);                                     \
    im13 = __SUMDOTP2(temp11, cd13, im13);                                     \
    im00 = im00 >> 15;                                                         \
    im01 = im01 >> 15;                                                         \
    im02 = im02 >> 15;                                                         \
    im03 = im03 >> 15;                                                         \
    im10 = im10 >> 15;                                                         \
    im11 = im11 >> 15;                                                         \
    im12 = im12 >> 15;                                                         \
    im13 = im13 >> 15;                                                         \
    temp00 = __EXOR2(ab00, (v2s)(0x0000FFFF));                                 \
    temp01 = __EXOR2(ab01, (v2s)(0x0000FFFF));                                 \
    temp10 = __EXOR2(ab10, (v2s)(0x0000FFFF));                                 \
    temp11 = __EXOR2(ab11, (v2s)(0x0000FFFF));                                 \
    temp00 = __ADD2(temp00, (v2s)(0x00000001));                                \
    temp01 = __ADD2(temp01, (v2s)(0x00000001));                                \
    temp10 = __ADD2(temp10, (v2s)(0x00000001));                                \
    temp11 = __ADD2(temp11, (v2s)(0x00000001));                                \
    re00 = __DOTP2(temp00, cd00);                                              \
    re01 = __DOTP2(temp00, cd01);                                              \
    re02 = __DOTP2(temp00, cd02);                                              \
    re03 = __DOTP2(temp00, cd03);                                              \
    re10 = __DOTP2(temp10, cd00);                                              \
    re11 = __DOTP2(temp10, cd01);                                              \
    re12 = __DOTP2(temp10, cd02);                                              \
    re13 = __DOTP2(temp10, cd03);                                              \
    re00 = __SUMDOTP2(temp01, cd10, re00);                                     \
    re01 = __SUMDOTP2(temp01, cd11, re01);                                     \
    re02 = __SUMDOTP2(temp01, cd12, re02);                                     \
    re03 = __SUMDOTP2(temp01, cd13, re03);                                     \
    re10 = __SUMDOTP2(temp11, cd10, re10);                                     \
    re11 = __SUMDOTP2(temp11, cd11, re11);                                     \
    re12 = __SUMDOTP2(temp11, cd12, re12);                                     \
    re13 = __SUMDOTP2(temp11, cd13, re13);                                     \
    re00 = re00 >> 15;                                                         \
    re01 = re01 >> 15;                                                         \
    re02 = re02 >> 15;                                                         \
    re03 = re03 >> 15;                                                         \
    re10 = re10 >> 15;                                                         \
    re11 = re11 >> 15;                                                         \
    re12 = re12 >> 15;                                                         \
    re13 = re13 >> 15;                                                         \
    v2s c00 = __PACK2(re00, im00);                                             \
    v2s c01 = __PACK2(re01, im01);                                             \
    v2s c02 = __PACK2(re02, im02);                                             \
    v2s c03 = __PACK2(re03, im03);                                             \
    v2s c10 = __PACK2(re10, im10);                                             \
    v2s c11 = __PACK2(re11, im11);                                             \
    v2s c12 = __PACK2(re12, im12);                                             \
    v2s c13 = __PACK2(re13, im13);                                             \
    sum00 = __ADD2(sum00, c00);                                                \
    sum01 = __ADD2(sum01, c01);                                                \
    sum02 = __ADD2(sum02, c02);                                                \
    sum03 = __ADD2(sum03, c03);                                                \
    sum10 = __ADD2(sum10, c10);                                                \
    sum11 = __ADD2(sum11, c11);                                                \
    sum12 = __ADD2(sum12, c12);                                                \
    sum13 = __ADD2(sum13, c13);                                                \
  }                                                                            \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 0)]) = sum00;                             \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 1)]) = sum01;                             \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 2)]) = sum02;                             \
  (*(v2s *)&C[2 * ((i + 0) * P + k + 3)]) = sum03;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 0)]) = sum10;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 1)]) = sum11;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 2)]) = sum12;                             \
  (*(v2s *)&C[2 * ((i + 1) * P + k + 3)]) = sum13;

void cmatmul_2x4_q16s(int16_t const *__restrict__ A,
                      int16_t const *__restrict__ B, int16_t *__restrict__ C,
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

void cmatmul_2x4_q16p(int16_t const *__restrict__ A,
                      int16_t const *__restrict__ B, int16_t *__restrict__ C,
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
  uint32_t shift_id = 2 * (core_id % NUM_CORES_PER_TILE);
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = shift_id; i < M; i += 2) {
      CMATMUL_2x4_LOOP;
    }
    for (i = 0; i < shift_id; i += 2) {
      CMATMUL_2x4_LOOP;
    }
  }
#endif
  mempool_barrier(numThreads);
  return;
}
