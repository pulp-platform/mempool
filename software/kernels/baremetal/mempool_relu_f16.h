// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

void relu_f16(__fp16 *__restrict__ DPtr, uint32_t size_N, uint32_t core_id,
              uint32_t numThreads) {
  uint32_t i, j;
  for (i = core_id * 2 * BANKING_FACTOR; i < size_N;
       i += numThreads * 2 * BANKING_FACTOR) {
    v2h x1, x2, x3, x4;
    v2h x5, x6, x7, x8;
    switch (BANKING_FACTOR) {
    case 4:
      x1 = *(v2h *)&DPtr[i];
      x2 = *(v2h *)&DPtr[i + 2];
      x3 = *(v2h *)&DPtr[i + 4];
      x4 = *(v2h *)&DPtr[i + 6];
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x1));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x2));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x3));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x4));
      *(v2h *)&DPtr[i] = x1;
      *(v2h *)&DPtr[i + 2] = x2;
      *(v2h *)&DPtr[i + 4] = x3;
      *(v2h *)&DPtr[i + 6] = x4;
      break;
    case 8:
      x1 = *(v2h *)&DPtr[i];
      x2 = *(v2h *)&DPtr[i + 2];
      x3 = *(v2h *)&DPtr[i + 4];
      x4 = *(v2h *)&DPtr[i + 6];
      x5 = *(v2h *)&DPtr[i + 8];
      x6 = *(v2h *)&DPtr[i + 10];
      x7 = *(v2h *)&DPtr[i + 12];
      x8 = *(v2h *)&DPtr[i + 14];
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x1));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x2));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x3));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x4));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x5));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x6));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x7));
      asm volatile("vfmax.h %0, %0, zero" : "+r"(x8));
      *(v2h *)&DPtr[i] = x1;
      *(v2h *)&DPtr[i + 2] = x2;
      *(v2h *)&DPtr[i + 4] = x3;
      *(v2h *)&DPtr[i + 6] = x4;
      *(v2h *)&DPtr[i + 8] = x5;
      *(v2h *)&DPtr[i + 10] = x6;
      *(v2h *)&DPtr[i + 12] = x7;
      *(v2h *)&DPtr[i + 14] = x8;
      break;
    default:
      for (j = 0; j < 2 * BANKING_FACTOR; j += 2) {
        v2h x = *(v2h *)&DPtr[i + j];
        asm volatile("vfmax.h %0, %0, zero" : "+r"(x));
        *(v2h *)&DPtr[i + j] = x;
      }
    }
  }
  return;
}
