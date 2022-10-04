// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "mempool_sqrt_q32s.h"
#include "xpulp/builtins_v2.h"

int32_t mempool_sqrt_q32s(int32_t Src, const uint32_t fracBits);

void mempool_cholesky_q32s(int32_t *pSrc, int32_t *pL, const uint32_t n,
                           const uint32_t fracBits);

void mempool_cholesky_q32s(int32_t *pSrc, int32_t *pL, const uint32_t n,
                           const uint32_t fracBits) {

  register int32_t sum, sumR, sumI;
  int32_t diag = 0;
  int16_t t = 0, PR = 0, PI = 0;
  uint32_t i, j, k;

  v2s a0, a1, a2, a3;
  v2s b0, b1, b2, b3;
  v2s X, Y, P, D = (v2s){0, 0};

  for (j = 0; j < n; j++) {

    diag = pSrc[j * n + j];
    sum = 0;
    for (k = 0; k < 4 * (j >> 2U); k++) {
      a0 = *(v2s *)&pL[j * n + k];
      a1 = *(v2s *)&pL[j * n + k + 1];
      a2 = *(v2s *)&pL[j * n + k + 2];
      a3 = *(v2s *)&pL[j * n + k + 3];
      asm volatile("pv.dotsp.h  %[sum],%[a0],%[a0];"
                   "pv.dotsp.h  %[sum],%[a1],%[a1];"
                   "pv.dotsp.h  %[sum],%[a2],%[a2];"
                   "pv.dotsp.h  %[sum],%[a3],%[a3];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                     [a3] "+&r"(a3), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
    }
    switch (j % 4) {
    case 3:
      a0 = *(v2s *)&pL[j * n + k];
      a1 = *(v2s *)&pL[j * n + k + 1];
      a2 = *(v2s *)&pL[j * n + k + 2];
      asm volatile(
          "pv.dotsp.h  %[sum],%[a0],%[a0];"
          "pv.dotsp.h  %[sum],%[a1],%[a1];"
          "pv.dotsp.h  %[sum],%[a2],%[a2];"
          : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [sum] "+&r"(sum)
          : [s] "I"(FIXED_POINT), [h] "I"(HALF)
          :);
      break;
    case 2:
      a0 = *(v2s *)&pL[j * n + k];
      a1 = *(v2s *)&pL[j * n + k + 1];
      asm volatile("pv.dotsp.h  %[sum],%[a0],%[a0];"
                   "pv.dotsp.h  %[sum],%[a1],%[a1];"
                   : [a0] "+&r"(a0), [a1] "+&r"(a1), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 1:
      a0 = *(v2s *)&pL[j * n + k];
      asm volatile("pv.dotsp.h  %[sum],%[a0],%[a0];"
                   : [a0] "+&r"(a0), [sum] "+&r"(sum)
                   : [s] "I"(FIXED_POINT), [h] "I"(HALF)
                   :);
      break;
    case 0:
      break;
    }
    pL[j * n + j] = mempool_sqrt_q32s((diag - sum), fracBits);

    for (i = j + 1; i < n; i++) {
      sumR = 0;
      sumI = 0;
      diag = pL[j * n + j];
      P = *(v2s *)&pSrc[i * n + j];
      for (k = 0; k < 4 * (j >> 2U); k += 4) {
        a0 = *(v2s *)&pL[i * n + k];
        b0 = *(v2s *)&pL[j * n + k];
        a1 = *(v2s *)&pL[i * n + k + 1];
        b1 = *(v2s *)&pL[j * n + k + 1];
        a2 = *(v2s *)&pL[i * n + k + 2];
        b2 = *(v2s *)&pL[j * n + k + 2];
        a3 = *(v2s *)&pL[i * n + k + 3];
        b3 = *(v2s *)&pL[j * n + k + 3];
        asm volatile("pv.extract.h  %[t], %[b0], 0;"
                     "sub         %[t],  zero, %[t];"
                     "pv.shuffle2.h %[X], %[b0], %[pt];"
                     "pv.insert.h   %[Y], %[t], 0;"
                     "pv.dotsp.h  %[sumR],%[a0],%[X];"
                     "pv.dotsp.h  %[sumI],%[a0],%[Y];"

                     "pv.extract.h  %[t], %[b1], 0;"
                     "sub         %[t],  zero, %[t];"
                     "pv.shuffle2.h %[X], %[b1], %[pt];"
                     "pv.insert.h   %[Y], %[t], 0;"
                     "pv.dotsp.h  %[sumR],%[a1],%[X];"
                     "pv.dotsp.h  %[sumI],%[a1],%[Y];"

                     "pv.extract.h  %[t], %[b2], 0;"
                     "sub         %[t],  zero, %[t];"
                     "pv.shuffle2.h %[X], %[b2], %[pt];"
                     "pv.insert.h   %[Y], %[t], 0;"
                     "pv.dotsp.h  %[sumR],%[a2],%[X];"
                     "pv.dotsp.h  %[sumI],%[a2],%[Y];"

                     "pv.extract.h  %[t], %[b3], 0;"
                     "sub         %[t],  zero, %[t];"
                     "pv.shuffle2.h %[X], %[b3], %[pt];"
                     "pv.insert.h   %[Y], %[t], 0;"
                     "pv.dotsp.h  %[sumR],%[a3],%[X];"
                     "pv.dotsp.h  %[sumI],%[a3],%[Y];"
                     : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2),
                       [a3] "+&r"(a3), [X] "=&r"(X), [Y] "=&r"(Y), [t] "=&r"(t),
                       [sumR] "+&r"(sumR), [sumI] "+&r"(sumI)
                     : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [b3] "r"(b3),
                       [pt] "r"((v2s){0, 1})
                     :);
      }
      switch (j % 4) {
      case 3:
        a0 = *(v2s *)&pL[i * n + k];
        b0 = *(v2s *)&pL[j * n + k];
        a1 = *(v2s *)&pL[i * n + k + 1];
        b1 = *(v2s *)&pL[j * n + k + 1];
        a2 = *(v2s *)&pL[i * n + k + 2];
        b2 = *(v2s *)&pL[j * n + k + 2];
        asm volatile(
            "pv.extract.h  %[t], %[b0], 0;"
            "sub         %[t],  zero, %[t];"
            "pv.shuffle2.h %[X], %[b0], %[pt];"
            "pv.insert.h   %[Y], %[t], 0;"
            "pv.dotsp.h  %[sumR],%[a0],%[X];"
            "pv.dotsp.h  %[sumI],%[a0],%[Y];"

            "pv.extract.h  %[t], %[b1], 0;"
            "sub         %[t],  zero, %[t];"
            "pv.shuffle2.h %[X], %[b1], %[pt];"
            "pv.insert.h   %[Y], %[t], 0;"
            "pv.dotsp.h  %[sumR],%[a1],%[X];"
            "pv.dotsp.h  %[sumI],%[a1],%[Y];"

            "pv.extract.h  %[t], %[b2], 0;"
            "sub         %[t],  zero, %[t];"
            "pv.shuffle2.h %[X], %[b2], %[pt];"
            "pv.insert.h   %[Y], %[t], 0;"
            "pv.dotsp.h  %[sumR],%[a2],%[X];"
            "pv.dotsp.h  %[sumI],%[a2],%[Y];"
            : [a0] "+&r"(a0), [a1] "+&r"(a1), [a2] "+&r"(a2), [X] "=&r"(X),
              [Y] "=&r"(Y), [t] "=&r"(t), [sumR] "+&r"(sumR), [sumI] "+&r"(sumI)
            : [b0] "r"(b0), [b1] "r"(b1), [b2] "r"(b2), [pt] "r"((v2s){0, 1})
            :);
        break;
      case 2:
        a0 = *(v2s *)&pL[i * n + k];
        b0 = *(v2s *)&pL[j * n + k];
        a1 = *(v2s *)&pL[i * n + k + 1];
        b1 = *(v2s *)&pL[j * n + k + 1];
        asm volatile(
            "pv.extract.h  %[t], %[b0], 0;"
            "sub         %[t],  zero, %[t];"
            "pv.shuffle2.h %[X], %[b0], %[pt];"
            "pv.insert.h   %[Y], %[t], 0;"
            "pv.dotsp.h  %[sumR],%[a0],%[X];"
            "pv.dotsp.h  %[sumI],%[a0],%[Y];"

            "pv.extract.h  %[t], %[b1], 0;"
            "sub         %[t],  zero, %[t];"
            "pv.shuffle2.h %[X], %[b1], %[pt];"
            "pv.insert.h   %[Y], %[t], 0;"
            "pv.dotsp.h  %[sumR],%[a1],%[X];"
            "pv.dotsp.h  %[sumI],%[a1],%[Y];"

            : [a0] "+&r"(a0), [a1] "+&r"(a1), [X] "=&r"(X), [Y] "=&r"(Y),
              [t] "=&r"(t), [sumR] "+&r"(sumR), [sumI] "+&r"(sumI)
            : [b0] "r"(b0), [b1] "r"(b1), [pt] "r"((v2s){0, 1})
            :);
        break;
      case 1:
        a0 = *(v2s *)&pL[i * n + k];
        b0 = *(v2s *)&pL[j * n + k];
        asm volatile("pv.extract.h  %[t], %[b0], 0;"
                     "sub         %[t],  zero, %[t];"
                     "pv.shuffle2.h %[X], %[b0], %[pt];"
                     "pv.insert.h   %[Y], %[t],  0;"
                     "pv.dotsp.h  %[sumR],%[a0],%[X];"
                     "pv.dotsp.h  %[sumI],%[a0],%[Y];"
                     : [a0] "+&r"(a0), [X] "=&r"(X), [Y] "=&r"(Y), [t] "=&r"(t),
                       [sumR] "+&r"(sumR), [sumI] "+&r"(sumI)
                     : [b0] "r"(b0), [pt] "r"((v2s){0, 1})
                     :);
        break;
      case 0:
        break;
      }
      if (i >= (j + 2))
        *(v2s *)&pL[(i - 1) * n + j] = D;

      asm volatile("pv.extract.h  %[PR], %[P], 0;"
                   "pv.extract.h  %[PI], %[P], 1;"
                   "sub         %[sumR], %[PR], %[sumR];"
                   "sub         %[sumI], %[PI], %[sumI];"
                   "div         %[sumR], %[sumR], %[diag];"
                   "div         %[sumI], %[sumI], %[diag];"
                   "pv.pack.h   %[D], %[sumR], %[sumI];"
                   : [P] "+&r"(P), [PR] "=&r"(PR), [PI] "=&r"(PI), [D] "=&r"(D),
                     [sumR] "+&r"(sumR), [sumI] "+&r"(sumI)
                   : [diag] "r"(diag)
                   :);
    }
    *(v2s *)&pL[(i - 1) * n + j] = D;
  }
}
