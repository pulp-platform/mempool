// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#define MIN(x, y) (((x) < (y)) ? (x) : (y))
#include "xpulp/builtins_v2.h"

void mempool_radix2_butterfly_q16p(int16_t *pSrc16, uint32_t fftLen,
                                   int16_t *pCoef16, uint32_t nPE) {

  uint32_t i, j, k, l;
  uint32_t n1, n2, ia;
  uint32_t core_id = mempool_get_core_id();
  uint32_t step, steps, butt_id, offset;
  v2s T, S, R;
  v2s coeff;
  int16_t out1, out2;
  uint32_t twidCoefModifier = 1;

  n1 = fftLen;
  n2 = n1 >> 1;
  step = (n2 + nPE - 1) / nPE;

  // loop for groups
  for (i = core_id * step; i < MIN(core_id * step + step, n2); i++) {

    coeff = *(v2s *)&pCoef16[i * 2U];

    /* Reading i and i+fftLen/2 inputs */
    /* Input is downscaled by 1 to avoid overflow */
    l = i + n2;
    /* Read ya (real), xa (imag) input */
    T = __SRA2(*(v2s *)&pSrc16[i * 2U], ((v2s){1, 1}));
    /* Read yb (real), xb (imag) input */
    S = __SRA2(*(v2s *)&pSrc16[l * 2U], ((v2s){1, 1}));

    /* R0 = (ya - yb) */
    /* R1 = (xa - xb) */
    R = __SUB2(T, S);

    /*  writing the butterfly processed i sample */
    /* ya' = ya + yb */
    /* xa' = xa + xb */
    *((v2s *)&pSrc16[i * 2U]) = __SRA2(__ADD2(T, S), ((v2s){1, 1}));

    /* out1 = (ya - yb)*cos + (xa - xb)*sin */
    /* out2 = (ya - yb)*cos - (xa - xb)*sin */
    out1 = (int16_t)(__DOTP2(R, coeff) >> 16U);
    out2 = (int16_t)(__DOTP2(R, __PACK2(coeff[0], -coeff[1])) >> 16U);
    *((v2s *)&pSrc16[l * 2U]) = __PACK2(out2, out1);

  } /* groups loop end */
  mempool_barrier(nPE);

  twidCoefModifier = twidCoefModifier << 1U;
  /* loop for stage */
  for (k = fftLen / 2; k > 2; k = k >> 1) {
    n1 = n2;
    n2 = n2 >> 1;
    step = (n2 + nPE - 1) / nPE;
    butt_id = core_id % n2;
    offset = (core_id / n2) * n1;
    ia = butt_id * step;

    /* loop for groups */
    for (j = butt_id * step; j < MIN(butt_id * step + step, n2); j++) {
      ia = twidCoefModifier * j;
      coeff = *(v2s *)&pCoef16[ia * 2U];

      /* loop for butterfly */
      for (i = offset + j; i < fftLen; i += ((nPE + n2 - 1) / n2) * n1) {

        /* Reading i and i+fftLen/2 inputs */
        /* Input is downscaled by 1 to avoid overflow */
        l = i + n2;
        /* Read ya (real), xa (imag) input */
        T = *(v2s *)&pSrc16[i * 2U];
        /* Read yb (real), xb (imag) input */
        S = *(v2s *)&pSrc16[l * 2U];
        /* R0 = (ya - yb) */
        /* R1 = (xa - xb) */
        R = __SUB2(T, S);
        /*  writing the butterfly processed i sample */
        /* ya' = ya + yb */
        /* xa' = xa + xb */
        *((v2s *)&pSrc16[i * 2U]) = __SRA2(__ADD2(T, S), ((v2s){1, 1}));
        /* out1 = (ya - yb)*cos + (xa - xb)*sin */
        /* out2 = (ya - yb)*cos - (xa - xb)*sin */
        out1 = (int16_t)(__DOTP2(R, coeff) >> 16U);
        out2 = (int16_t)(__DOTP2(R, __PACK2(coeff[0], -coeff[1])) >> 16U);
        *((v2s *)&pSrc16[l * 2U]) = __PACK2(out2, out1);

      } /* butterfly loop end */

    } /* groups loop end */

    twidCoefModifier <<= 1U;
    mempool_barrier(nPE);
  } /* stages loop end */

  n1 = n2;
  n2 = n2 >> 1;
  steps = fftLen / n1;
  step = (steps + nPE - 1) / nPE;
  /* loop for butterfly */

  for (i = core_id * step * n1; i < MIN((core_id * step + step) * n1, fftLen);
       i += n1) {

    l = i + n2;
    /* Read ya (real), xa (imag) input */
    T = *(v2s *)&pSrc16[i * 2U];
    /* Read yb (real), xb (imag) input */
    S = *(v2s *)&pSrc16[l * 2U];
    /* ya' = ya + yb */
    /* xa' = xa + xb */
    *((v2s *)&pSrc16[i * 2U]) = __ADD2(T, S);
    /* yb' = ya - yb */
    /* xb' = xa - xb */
    *((v2s *)&pSrc16[l * 2U]) = __SUB2(T, S);

  } /* groups loop end */
  mempool_barrier(nPE);
}

void mempool_radix2_bitreversal_q16p(int16_t *pSrc, const uint16_t bitRevLen,
                                     const uint16_t *pBitRevTab, uint32_t nPE) {
  uint32_t i;
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  v2s addr, tmpa, tmpb;

  for (i = core_id * 2; i < bitRevLen; i += nPE * 2) {
    addr = __SRA2(*(v2s *)&pBitRevTab[i], ((v2s){2, 2}));
    tmpa = *(v2s *)&pSrc[addr[0]];
    tmpb = *(v2s *)&pSrc[addr[1]];
    *((v2s *)&pSrc[addr[0]]) = tmpb;
    *((v2s *)&pSrc[addr[1]]) = tmpa;
  }
  mempool_barrier(num_cores);
}
