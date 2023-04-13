// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"

static void mempool_radix4_cfft_q16s_riscv32(int16_t *pIn, uint32_t fftLen,
                                             int16_t *pCoef16,
                                             uint32_t twidCoefModifier) {

  int16_t R0, R1, S0, S1, T0, T1, U0, U1;
  int16_t Co1, Si1, Co2, Si2, Co3, Si3, out1, out2;
  uint32_t n1, n2, ic, i0, i1, i2, i3, j, k;

  /* START OF FIRST STAGE PROCESS */
  n2 = fftLen;
  n1 = n2;
  n2 >>= 2U;
  ic = 0U;
  for (i0 = 0; i0 < n2; i0++) {

    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;

    /* Reading i0, i0+fftLen/2 inputs */
    /* input is down scale by 4 to avoid overflow */
    /* Read ya (real), xa (imag) input */
    T0 = pIn[i0 * 2U] >> 2U;
    T1 = pIn[(i0 * 2U) + 1U] >> 2U;
    /* input is down scale by 4 to avoid overflow */
    /* Read yc (real), xc(imag) input */
    S0 = pIn[i2 * 2U] >> 2U;
    S1 = pIn[(i2 * 2U) + 1U] >> 2U;
    /* R0 = (ya + yc) */
    R0 = (int16_t)__CLIP(T0 + S0, 15);
    /* R1 = (xa + xc) */
    R1 = (int16_t)__CLIP(T1 + S1, 15);
    /* S0 = (ya - yc) */
    S0 = (int16_t)__CLIP(T0 - S0, 15);
    /* S1 = (xa - xc) */
    S1 = (int16_t)__CLIP(T1 - S1, 15);
    /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
    /* input is down scale by 4 to avoid overflow */
    /* Read yb (real), xb(imag) input */
    T0 = pIn[i1 * 2U] >> 2U;
    T1 = pIn[(i1 * 2U) + 1U] >> 2U;
    /* input is down scale by 4 to avoid overflow */
    /* Read yd (real), xd(imag) input */
    U0 = pIn[i3 * 2U] >> 2U;
    U1 = pIn[(i3 * 2U) + 1U] >> 2U;
    /* T0 = (yb + yd) */
    T0 = (int16_t)__CLIP(T0 + U0, 15);
    /* T1 = (xb + xd) */
    T1 = (int16_t)__CLIP(T1 + U1, 15);
    /*  writing the butterfly processed i0 sample */
    /* ya' = ya + yb + yc + yd */
    /* xa' = xa + xb + xc + xd */
    pIn[i0 * 2] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
    pIn[(i0 * 2) + 1] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
    /* R0 = (ya + yc) - (yb + yd) */
    /* R1 = (xa + xc) - (xb + xd) */
    R0 = (int16_t)__CLIP(R0 - T0, 15);
    R1 = (int16_t)__CLIP(R1 - T1, 15);
    /* co2 & si2 are read from Coefficient pointer */
    Co2 = pCoef16[2U * ic * 2U];
    Si2 = pCoef16[(2U * ic * 2U) + 1];
    /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
    out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
    /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
    out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
    /*  Reading i0+fftLen/4 */
    /* input is down scale by 4 to avoid overflow */
    /* T0 = yb, T1 =  xb */
    T0 = pIn[i1 * 2U] >> 2;
    T1 = pIn[(i1 * 2U) + 1] >> 2;
    /* writing the butterfly processed i0 + fftLen/4 sample */
    /* writing output(xc', yc') in little endian format */
    pIn[i1 * 2U] = out1;
    pIn[(i1 * 2U) + 1] = out2;
    /*  Butterfly calculations */
    /* input is down scale by 4 to avoid overflow */
    /* U0 = yd, U1 = xd */
    U0 = pIn[i3 * 2U] >> 2;
    U1 = pIn[(i3 * 2U) + 1] >> 2;
    /* T0 = yb-yd */
    T0 = (int16_t)__CLIP(T0 - U0, 15);
    /* T1 = xb-xd */
    T1 = (int16_t)__CLIP(T1 - U1, 15);
    /* R1 = (ya-yc) + (xb- xd),  R0 = (xa-xc) - (yb-yd)) */
    R0 = (int16_t)__CLIP((int32_t)(S0 - T1), 15);
    R1 = (int16_t)__CLIP((int32_t)(S1 + T0), 15);
    /* S1 = (ya-yc) - (xb- xd), S0 = (xa-xc) + (yb-yd)) */
    S0 = (int16_t)__CLIP(((int32_t)S0 + T1), 15);
    S1 = (int16_t)__CLIP(((int32_t)S1 - T0), 15);
    /* co1 & si1 are read from Coefficient pointer */
    Co1 = pCoef16[ic * 2U];
    Si1 = pCoef16[(ic * 2U) + 1];
    /*  Butterfly process for the i0+fftLen/2 sample */
    /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
    out1 = (int16_t)((Si1 * S1 + Co1 * S0) >> 16);
    /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
    out2 = (int16_t)((-Si1 * S0 + Co1 * S1) >> 16);
    /* writing output(xb', yb') in little endian format */
    pIn[i2 * 2U] = out1;
    pIn[(i2 * 2U) + 1] = out2;
    /* Co3 & si3 are read from Coefficient pointer */
    Co3 = pCoef16[3U * (ic * 2U)];
    Si3 = pCoef16[(3U * (ic * 2U)) + 1];
    /*  Butterfly process for the i0+3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
    out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
    /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
    out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
    /* writing output(xd', yd') in little endian format */
    pIn[i3 * 2U] = out1;
    pIn[(i3 * 2U) + 1] = out2;

    /*  Twiddle coefficients index modifier */
    ic = ic + twidCoefModifier;
  };
  /* END OF FIRST STAGE PROCESS */

  /* START OF MIDDLE STAGE PROCESS */
  twidCoefModifier <<= 2U;
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {

    /*  Initializations for the middle stage */
    n1 = n2;
    n2 >>= 2U;
    ic = 0U;
    for (j = 0U; j <= (n2 - 1U); j++) {

      /*  index calculation for the coefficients */
      Co1 = pCoef16[ic * 2U];
      Si1 = pCoef16[(ic * 2U) + 1U];
      Co2 = pCoef16[2U * (ic * 2U)];
      Si2 = pCoef16[(2U * (ic * 2U)) + 1U];
      Co3 = pCoef16[3U * (ic * 2U)];
      Si3 = pCoef16[(3U * (ic * 2U)) + 1U];
      /*  Twiddle coefficients index modifier */
      ic = ic + twidCoefModifier;

      /*  Butterfly implementation */
      for (i0 = j; i0 < fftLen; i0 += n1) {

        i1 = i0 + n2;
        i2 = i1 + n2;
        i3 = i2 + n2;

        /*  Reading i0, i0+fftLen/2 inputs */
        /* Read ya (real), xa(imag) input */
        T0 = pIn[i0 * 2U];
        T1 = pIn[(i0 * 2U) + 1U];
        /* Read yc (real), xc(imag) input */
        S0 = pIn[i2 * 2U];
        S1 = pIn[(i2 * 2U) + 1U];
        /* R0 = (ya + yc), R1 = (xa + xc) */
        R0 = (int16_t)__CLIP(T0 + S0, 15);
        R1 = (int16_t)__CLIP(T1 + S1, 15);
        /* S0 = (ya - yc), S1 =(xa - xc) */
        S0 = (int16_t)__CLIP(T0 - S0, 15);
        S1 = (int16_t)__CLIP(T1 - S1, 15);
        /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
        /* Read yb (real), xb(imag) input */
        T0 = pIn[i1 * 2U];
        T1 = pIn[(i1 * 2U) + 1U];
        /* Read yd (real), xd(imag) input */
        U0 = pIn[i3 * 2U];
        U1 = pIn[(i3 * 2U) + 1U];
        /* T0 = (yb + yd), T1 = (xb + xd) */
        T0 = (int16_t)__CLIP(T0 + U0, 15);
        T1 = (int16_t)__CLIP(T1 + U1, 15);
        /*  writing the butterfly processed i0 sample */
        /* xa' = xa + xb + xc + xd */
        /* ya' = ya + yb + yc + yd */
        out1 = (int16_t)(((R0 >> 1U) + (T0 >> 1U)) >> 1U);
        out2 = (int16_t)(((R1 >> 1U) + (T1 >> 1U)) >> 1U);
        pIn[i0 * 2U] = out1;
        pIn[(2U * i0) + 1U] = out2;
        /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
        R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
        R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
        /* (ya-yb+yc-yd)* (si2) + (xa-xb+xc-xd)* co2 */
        out1 = (int16_t)((Co2 * R0 + Si2 * R1) >> 16U);
        /* (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
        out2 = (int16_t)((-Si2 * R0 + Co2 * R1) >> 16U);
        /*  Reading i0+3fftLen/4 */
        /* Read yb (real), xb(imag) input */
        T0 = pIn[i1 * 2U];
        T1 = pIn[(i1 * 2U) + 1U];
        /*  writing the butterfly processed i0 + fftLen/4 sample */
        /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
        /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
        pIn[i1 * 2U] = out1;
        pIn[(i1 * 2U) + 1U] = out2;
        /*  Butterfly calculations */
        /* Read yd (real), xd(imag) input */
        U0 = pIn[i3 * 2U];
        U1 = pIn[(i3 * 2U) + 1U];
        /* T0 = yb-yd, T1 = xb-xd */
        T0 = (int16_t)__CLIP(T0 - U0, 15);
        T1 = (int16_t)__CLIP(T1 - U1, 15);
        /* R0 = (ya-yc) + (xb- xd), R1 = (xa-xc) - (yb-yd)) */
        R0 = (int16_t)((S0 >> 1U) - (T1 >> 1U));
        R1 = (int16_t)((S1 >> 1U) + (T0 >> 1U));
        /* S0 = (ya-yc) - (xb- xd), S1 = (xa-xc) + (yb-yd)) */
        S0 = (int16_t)((S0 >> 1U) + (T1 >> 1U));
        S1 = (int16_t)((S1 >> 1U) - (T0 >> 1U));
        /*  Butterfly process for the i0+fftLen/2 sample */
        out1 = (int16_t)((Co1 * S0 + Si1 * S1) >> 16U);
        out2 = (int16_t)((-Si1 * S0 + Co1 * S1) >> 16U);
        /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
        /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
        pIn[i2 * 2U] = out1;
        pIn[(i2 * 2U) + 1U] = out2;
        /*  Butterfly process for the i0+3fftLen/4 sample */
        out1 = (int16_t)((Si3 * R1 + Co3 * R0) >> 16U);
        out2 = (int16_t)((-Si3 * R0 + Co3 * R1) >> 16U);
        /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
        /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
        pIn[i3 * 2U] = out1;
        pIn[(i3 * 2U) + 1U] = out2;
      }
    }
    /*  Twiddle coefficients index modifier */
    twidCoefModifier <<= 2U;
  }
  /* END OF MIDDLE STAGE PROCESSING */

  /* START OF LAST STAGE PROCESSING */
  n1 = n2;
  n2 >>= 2U;
  for (i0 = 0U; i0 < fftLen; i0 += n1) {

    i1 = i0 + n2;
    i2 = i1 + n2;
    i3 = i2 + n2;

    /*  Reading i0, i0+fftLen/2 inputs */
    /* Read ya (real), xa(imag) input */
    T0 = pIn[i0 * 2U];
    T1 = pIn[(i0 * 2U) + 1U];
    /* Read yc (real), xc(imag) input */
    S0 = pIn[i2 * 2U];
    S1 = pIn[(i2 * 2U) + 1U];
    /* R0 = (ya + yc), R1 = (xa + xc) */
    R0 = (int16_t)__CLIP(T0 + S0, 15);
    R1 = (int16_t)__CLIP(T1 + S1, 15);
    /* S0 = (ya - yc), S1 = (xa - xc) */
    S0 = (int16_t)__CLIP(T0 - S0, 15);
    S1 = (int16_t)__CLIP(T1 - S1, 15);
    /*  Reading i0+fftLen/4 , i0+3fftLen/4 inputs */
    /* Read yb (real), xb(imag) input */
    T0 = pIn[i1 * 2U];
    T1 = pIn[(i1 * 2U) + 1U];
    /* Read yd (real), xd(imag) input */
    U0 = pIn[i3 * 2U];
    U1 = pIn[(i3 * 2U) + 1U];
    /* T0 = (yb + yd), T1 = (xb + xd)) */
    T0 = (int16_t)__CLIP(T0 + U0, 15);
    T1 = (int16_t)__CLIP(T1 + U1, 15);
    /*  writing the butterfly processed i0 sample */
    /* xa' = xa + xb + xc + xd */
    /* ya' = ya + yb + yc + yd */
    pIn[i0 * 2U] = (int16_t)((R0 >> 1U) + (T0 >> 1U));
    pIn[(i0 * 2U) + 1U] = (int16_t)((R1 >> 1U) + (T1 >> 1U));
    /* R0 = (ya + yc) - (yb + yd), R1 = (xa + xc) - (xb + xd) */
    R0 = (int16_t)((R0 >> 1U) - (T0 >> 1U));
    R1 = (int16_t)((R1 >> 1U) - (T1 >> 1U));
    /* Read yb (real), xb(imag) input */
    T0 = pIn[i1 * 2U];
    T1 = pIn[(i1 * 2U) + 1U];
    /*  writing the butterfly processed i0 + fftLen/4 sample */
    /* xc' = (xa-xb+xc-xd) */
    /* yc' = (ya-yb+yc-yd) */
    pIn[i1 * 2U] = R0;
    pIn[(i1 * 2U) + 1U] = R1;
    /* Read yd (real), xd(imag) input */
    U0 = pIn[i3 * 2U];
    U1 = pIn[(i3 * 2U) + 1U];
    /* T0 = (yb - yd), T1 = (xb - xd)  */
    T0 = (int16_t)__CLIP(T0 - U0, 15);
    T1 = (int16_t)__CLIP(T1 - U1, 15);
    /*  writing the butterfly processed i0 + fftLen/2 sample */
    /* xb' = (xa+yb-xc-yd) */
    /* yb' = (ya-xb-yc+xd) */
    pIn[i2 * 2U] = (int16_t)((S0 >> 1U) + (T1 >> 1U));
    pIn[(i2 * 2U) + 1U] = (int16_t)((S1 >> 1U) - (T0 >> 1U));
    /*  writing the butterfly processed i0 + 3fftLen/4 sample */
    /* xd' = (xa-yb-xc+yd) */
    /* yd' = (ya+xb-yc-xd) */
    pIn[i3 * 2U] = (int16_t)((S0 >> 1U) - (T1 >> 1U));
    pIn[(i3 * 2U) + 1U] = (int16_t)((S1 >> 1U) + (T0 >> 1U));
  }
  /* END OF LAST STAGE PROCESSING */
}

static void mempool_radix4_cfft_q16s_xpulpimg(int16_t *pSrc16, uint32_t fftLen,
                                              int16_t *pCoef16,
                                              uint32_t twidCoefModifier) {

  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;
  int16_t t0, t1, t2, t3, t4, t5;
  uint32_t n1, n2, ic, i0, j, k;

  n1 = fftLen;
  n2 = n1 >> 2U;

  /* START OF FIRST STAGE PROCESS */
  for (i0 = 0; i0 < n2; i0++) {
    CoSi1 = *(v2s *)&pCoef16[2U * i0];
    CoSi2 = *(v2s *)&pCoef16[2U * i0 * 2U];
    CoSi3 = *(v2s *)&pCoef16[2U * i0 * 3U];
#ifndef ASM
    t1 = (int16_t)CoSi1[0];
    t3 = (int16_t)CoSi2[0];
    t5 = (int16_t)CoSi3[0];
    t0 = (int16_t)CoSi1[1];
    t2 = (int16_t)CoSi2[1];
    t4 = (int16_t)CoSi3[1];
    C1 = __PACK2(t1, -t0);
    C2 = __PACK2(t3, -t2);
    C3 = __PACK2(t5, -t4);
#else
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "sub           %[t0],zero,%[t0];"
                 "sub           %[t2],zero,%[t2];"
                 "sub           %[t4],zero,%[t4];"
                 "pv.pack %[C1],%[t1],%[t0];"
                 "pv.pack %[C2],%[t3],%[t2];"
                 "pv.pack %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
#endif
    radix4_butterfly_first(pSrc16, pSrc16, i0, n2, CoSi1, CoSi2, CoSi3, C1, C2,
                           C3);
  }
  /* END OF FIRST STAGE PROCESS */

  /* START OF MIDDLE STAGE PROCESS */
  twidCoefModifier <<= 2U;
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {
    n1 = n2;
    n2 >>= 2U;
    ic = 0U;
    for (j = 0U; j <= (n2 - 1U); j++) {
      /*  index calculation for the coefficients */
      CoSi1 = *(v2s *)&pCoef16[ic * 2U];
      CoSi2 = *(v2s *)&pCoef16[2U * (ic * 2U)];
      CoSi3 = *(v2s *)&pCoef16[3U * (ic * 2U)];
#ifndef ASM
      t1 = (int16_t)CoSi1[0];
      t3 = (int16_t)CoSi2[0];
      t5 = (int16_t)CoSi3[0];
      t0 = (int16_t)CoSi1[1];
      t2 = (int16_t)CoSi2[1];
      t4 = (int16_t)CoSi3[1];
      C1 = __PACK2(t1, -t0);
      C2 = __PACK2(t3, -t2);
      C3 = __PACK2(t5, -t4);
#else
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "sub           %[t0],zero,%[t0];"
                   "sub           %[t2],zero,%[t2];"
                   "sub           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
#endif
      /*  Twiddle coefficients index modifier */
      ic = ic + twidCoefModifier;
      /*  Butterfly implementation */
      for (i0 = j; i0 < fftLen; i0 += n1) {
        radix4_butterfly_middle(pSrc16, pSrc16, i0, n2, CoSi1, CoSi2, CoSi3, C1,
                                C2, C3);
      }
    }
    twidCoefModifier <<= 2U;
  }
  /* END OF MIDDLE STAGE PROCESSING */

  /* START OF LAST STAGE PROCESSING */
  n1 = n2;
  n2 >>= 2U;
  for (i0 = 0U; i0 < fftLen; i0 += n1) {
    radix4_butterfly_last(pSrc16, pSrc16, i0);
  }
  /* END OF LAST STAGE PROCESSING */
}

void mempool_cfft_radix4by2_q16s_riscv32(int16_t *pSrc, uint32_t fftLen,
                                         const int16_t *pCoef) {

  uint32_t i;
  uint32_t n2;
  int16_t p0, p1, p2, p3;

  uint32_t l;
  int16_t xt, yt, cosVal, sinVal;

  n2 = fftLen >> 1;

  for (i = 0; i < n2; i++) {
    cosVal = pCoef[i * 2];
    sinVal = pCoef[(i * 2) + 1];

    l = i + n2;

    xt = (int16_t)((pSrc[2 * i] >> 1U) - (pSrc[2 * l] >> 1U));
    pSrc[2 * i] = (int16_t)(((pSrc[2 * i] >> 1U) + (pSrc[2 * l] >> 1U)) >> 1U);

    yt = (int16_t)((pSrc[2 * i + 1] >> 1U) - (pSrc[2 * l + 1] >> 1U));
    pSrc[2 * i + 1] =
        (int16_t)(((pSrc[2 * l + 1] >> 1U) + (pSrc[2 * i + 1] >> 1U)) >> 1U);

    pSrc[2U * l] = (int16_t)(((int16_t)(((int32_t)xt * cosVal) >> 16)) +
                             ((int16_t)(((int32_t)yt * sinVal) >> 16)));

    pSrc[2U * l + 1U] = (int16_t)(((int16_t)(((int32_t)yt * cosVal) >> 16)) -
                                  ((int16_t)(((int32_t)xt * sinVal) >> 16)));
  }

  // first col
  mempool_radix4_cfft_q16s_riscv32(pSrc, n2, (int16_t *)pCoef, 2U);
  // second col
  mempool_radix4_cfft_q16s_riscv32(pSrc + fftLen, n2, (int16_t *)pCoef, 2U);

  for (i = 0; i < (fftLen >> 1); i++) {
    p0 = pSrc[4 * i + 0];
    p1 = pSrc[4 * i + 1];
    p2 = pSrc[4 * i + 2];
    p3 = pSrc[4 * i + 3];

    p0 = (int16_t)(p0 << 1U);
    p1 = (int16_t)(p1 << 1U);
    p2 = (int16_t)(p2 << 1U);
    p3 = (int16_t)(p3 << 1U);

    pSrc[4 * i + 0] = p0;
    pSrc[4 * i + 1] = p1;
    pSrc[4 * i + 2] = p2;
    pSrc[4 * i + 3] = p3;
  }
}

void mempool_cfft_radix4by2_q16s_xpulpimg(int16_t *pSrc, uint32_t fftLen,
                                          const int16_t *pCoef) {

  uint32_t i;
  uint32_t n2;
  v2s pa, pb;

  uint32_t l;
  v2s CoSi;
  v2s a, b, t;
  int16_t testa, testb;

  n2 = fftLen >> 1;

  for (i = 0; i < n2; i++) {
    CoSi = *(v2s *)&pCoef[i * 2];
    l = i + n2;
    a = __SRA2(*(v2s *)&pSrc[2 * i], ((v2s){1, 1}));
    b = __SRA2(*(v2s *)&pSrc[2 * l], ((v2s){1, 1}));
    t = __SUB2(a, b);
    *((v2s *)&pSrc[i * 2]) = __SRA2(__ADD2(a, b), ((v2s){1, 1}));

    testa = (int16_t)(__DOTP2(t, CoSi) >> 16);
    testb = (int16_t)(__DOTP2(t, __PACK2(-CoSi[1], CoSi[0])) >> 16);
    *((v2s *)&pSrc[l * 2]) = __PACK2(testa, testb);
  }

  // first col
  mempool_radix4_cfft_q16s_xpulpimg(pSrc, n2, (int16_t *)pCoef, 2U);
  // second col
  mempool_radix4_cfft_q16s_xpulpimg(pSrc + fftLen, n2, (int16_t *)pCoef, 2U);

  for (i = 0; i < (fftLen >> 1); i++) {
    pa = *(v2s *)&pSrc[4 * i];
    pb = *(v2s *)&pSrc[4 * i + 2];

    pa = __SLL2(pa, ((v2s){1, 1}));
    pb = __SLL2(pb, ((v2s){1, 1}));

    *((v2s *)&pSrc[4 * i]) = pa;
    *((v2s *)&pSrc[4 * i + 2]) = pb;
  }
}

void mempool_radix4_cfft_q16s_scheduler(
    int16_t *pSrc16, uint16_t fftLen, int16_t *pCoef16, uint16_t *pBitRevTable,
    uint16_t bitReverseLen, uint8_t bitReverseFlag, uint32_t nFFTs) {

  /* Initializations for the first stage */
  int16_t t0, t1, t2, t3, t4, t5;
  uint32_t n1, n2, i0, ic, j, k, twidCoefModifier;
  v2s CoSi1, CoSi2, CoSi3;
  v2s C1, C2, C3;

  /* FIRST STAGE */
  n1 = fftLen;
  n2 = n1 >> 2U;
  for (i0 = 0; i0 < n2; i0++) {
    CoSi1 = *(v2s *)&pCoef16[2U * i0];
    CoSi2 = *(v2s *)&pCoef16[2U * i0 * 2U];
    CoSi3 = *(v2s *)&pCoef16[2U * i0 * 3U];
    asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                 "pv.extract.h  %[t3],%[CoSi2],0;"
                 "pv.extract.h  %[t5],%[CoSi3],0;"
                 "pv.extract.h  %[t0],%[CoSi1],1;"
                 "pv.extract.h  %[t2],%[CoSi2],1;"
                 "pv.extract.h  %[t4],%[CoSi3],1;"
                 "sub           %[t0],zero,%[t0];"
                 "sub           %[t2],zero,%[t2];"
                 "sub           %[t4],zero,%[t4];"
                 "pv.pack %[C1],%[t1],%[t0];"
                 "pv.pack %[C2],%[t3],%[t2];"
                 "pv.pack %[C3],%[t5],%[t4];"
                 : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3), [t0] "=&r"(t0),
                   [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                   [t4] "=&r"(t4), [t5] "=&r"(t5)
                 : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                 :);
    for (uint32_t idx_fft = 0; idx_fft < nFFTs; idx_fft++) {
      radix4_butterfly_first(pSrc16 + (int32_t)idx_fft * (2 * fftLen),
                             pSrc16 + (int32_t)idx_fft * (2 * fftLen), i0, n2,
                             CoSi1, CoSi2, CoSi3, C1, C2, C3);
    }
  }

  /* MIDDLE STAGE */
  twidCoefModifier = 4;
  for (k = fftLen / 4U; k > 4U; k >>= 2U) {
    n1 = n2;
    n2 >>= 2U;
    ic = 0U;
    for (j = 0U; j <= (n2 - 1U); j++) {
      CoSi1 = *(v2s *)&pCoef16[2U * ic];
      CoSi2 = *(v2s *)&pCoef16[2U * ic * 2U];
      CoSi3 = *(v2s *)&pCoef16[2U * ic * 3U];
      asm volatile("pv.extract.h  %[t1],%[CoSi1],0;"
                   "pv.extract.h  %[t3],%[CoSi2],0;"
                   "pv.extract.h  %[t5],%[CoSi3],0;"
                   "pv.extract.h  %[t0],%[CoSi1],1;"
                   "pv.extract.h  %[t2],%[CoSi2],1;"
                   "pv.extract.h  %[t4],%[CoSi3],1;"
                   "sub           %[t0],zero,%[t0];"
                   "sub           %[t2],zero,%[t2];"
                   "sub           %[t4],zero,%[t4];"
                   "pv.pack %[C1],%[t1],%[t0];"
                   "pv.pack %[C2],%[t3],%[t2];"
                   "pv.pack %[C3],%[t5],%[t4];"
                   : [C1] "=r"(C1), [C2] "=r"(C2), [C3] "=r"(C3),
                     [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2),
                     [t3] "=&r"(t3), [t4] "=&r"(t4), [t5] "=&r"(t5)
                   : [CoSi1] "r"(CoSi1), [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
                   :);
      ic = ic + twidCoefModifier;
      for (i0 = j; i0 < fftLen; i0 += n1) {
        for (uint32_t idx_fft = 0; idx_fft < nFFTs; idx_fft++) {
          radix4_butterfly_middle(pSrc16 + (int32_t)idx_fft * (2 * fftLen),
                                  pSrc16 + (int32_t)idx_fft * (2 * fftLen), i0,
                                  n2, CoSi1, CoSi2, CoSi3, C1, C2, C3);
        }
      }
    }
    twidCoefModifier <<= 2U;
  }

  /* LAST STAGE */
  n1 = n2;
  n2 >>= 2U;
  for (i0 = 0U; i0 < fftLen; i0 += n1) {
    for (uint32_t idx_fft = 0; idx_fft < nFFTs; idx_fft++) {
      radix4_butterfly_last(pSrc16 + (int32_t)idx_fft * (2 * fftLen),
                            pSrc16 + (int32_t)idx_fft * (2 * fftLen), i0);
    }
  }

  /* BITREVERSAL */
  if (bitReverseFlag) {
    v2s addr1, addr2, addr3, addr4;
    v2s s2 = (v2s){2, 2};
    v2s tmpa1, tmpa2, tmpa3, tmpa4;
    v2s tmpb1, tmpb2, tmpb3, tmpb4;
    int32_t a1, a2, a3, a4;
    int32_t b1, b2, b3, b4;
    uint16_t *ptr;
    for (uint32_t i = 0; i < bitReverseLen; i += 8) {
      addr1 = *(v2s *)&pBitRevTable[i];
      addr2 = *(v2s *)&pBitRevTable[i + 2];
      addr3 = *(v2s *)&pBitRevTable[i + 4];
      addr4 = *(v2s *)&pBitRevTable[i + 6];
      asm volatile("pv.sra.h  %[addr1],%[addr1],%[s2];"
                   "pv.sra.h  %[addr2],%[addr2],%[s2];"
                   "pv.sra.h  %[addr3],%[addr3],%[s2];"
                   "pv.sra.h  %[addr4],%[addr4],%[s2];"
                   "pv.extract.h  %[a1],%[addr1],0;"
                   "pv.extract.h  %[a2],%[addr2],0;"
                   "pv.extract.h  %[a3],%[addr3],0;"
                   "pv.extract.h  %[a4],%[addr4],0;"
                   "pv.extract.h  %[b1],%[addr1],1;"
                   "pv.extract.h  %[b2],%[addr2],1;"
                   "pv.extract.h  %[b3],%[addr3],1;"
                   "pv.extract.h  %[b4],%[addr4],1;"
                   : [a1] "=r"(a1), [a2] "=r"(a2), [a3] "=r"(a3), [a4] "=r"(a4),
                     [b1] "=r"(b1), [b2] "=r"(b2), [b3] "=r"(b3), [b4] "=r"(b4),
                     [addr1] "+r"(addr1), [addr2] "+r"(addr2),
                     [addr3] "+r"(addr3), [addr4] "+r"(addr4)
                   : [s2] "r"(s2)
                   :);
      ptr = (uint16_t *)pSrc16;
      for (uint32_t idx_fft = 0; idx_fft < nFFTs; idx_fft++) {
        tmpa1 = *(v2s *)&ptr[a1];
        tmpa2 = *(v2s *)&ptr[a2];
        tmpa3 = *(v2s *)&ptr[a3];
        tmpa4 = *(v2s *)&ptr[a4];
        tmpb1 = *(v2s *)&ptr[b1];
        tmpb2 = *(v2s *)&ptr[b2];
        tmpb3 = *(v2s *)&ptr[b3];
        tmpb4 = *(v2s *)&ptr[b4];
        *((v2s *)&ptr[a1]) = tmpb1;
        *((v2s *)&ptr[a2]) = tmpb2;
        *((v2s *)&ptr[a3]) = tmpb3;
        *((v2s *)&ptr[a4]) = tmpb4;
        *((v2s *)&ptr[b1]) = tmpa1;
        *((v2s *)&ptr[b2]) = tmpa2;
        *((v2s *)&ptr[b3]) = tmpa3;
        *((v2s *)&ptr[b4]) = tmpa4;
        ptr += (2 * fftLen);
      }
    }
  }
}
