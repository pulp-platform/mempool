// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
#define ASM
#include "builtins_v2.h"

/**
  @brief         First butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are
  interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/
static inline void radix4_butterfly_first(int16_t *pIn, int16_t *pOut,
                                          uint32_t i0, uint32_t n2, v2s CoSi1,
                                          v2s CoSi2, v2s CoSi3, v2s C1, v2s C2,
                                          v2s C3) {
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2s A, B, C, D, E, F, G, H;

// LOAD INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  /* index calculation for the input as, */
  /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + n2;
  i2 = i1 + n2;
  i3 = i2 + n2;
#else
  /* index calculation for the input as, */
  /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + n2;
  i2 = i1 + n2;
  i3 = i2 + n2;
#endif
// STORE INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  uint32_t n2_store = n2 >> 2U;
  i0_store = (i0 % n2_store) + (i0 / n2_store) * NUM_BANKS;
  i1_store = i0_store + n2_store;
  i2_store = i1_store + n2_store;
  i3_store = i2_store + n2_store;
#else
  i0_store = i0;
  i1_store = i1;
  i2_store = i2;
  i3_store = i3;
#endif

#ifndef ASM
  int16_t t0, t1, t2, t3, t4, t5;
  v2s s1 = {1, 1};
  v2s s2 = {2, 2};
  /* Read yb (real), xb(imag) input */
  B = __SRA2(*(v2s *)&pIn[i1 * 2U], s2);
  /* Read yd (real), xd(imag) input */
  D = __SRA2(*(v2s *)&pIn[i3 * 2U], s2);
  /* Read ya (real), xa (imag) input */
  A = __SRA2(*(v2s *)&pIn[i0 * 2U], s2);
  /* Read yc (real), xc(imag) input */
  C = __SRA2(*(v2s *)&pIn[i2 * 2U], s2);
  /* G0 = (yb + yd), G1 = (xb + xd) */
  G = __ADD2(B, D);
  /* H0 = (yb - yd), H1 = (xb - xd) */
  H = __SUB2(B, D);
  /* E0 = (ya + yc), E1 = (xa + xc) */
  E = __ADD2(A, C);
  /* F0 = (ya - yc), F1 = (xa - xc) */
  F = __SUB2(A, C);
  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];
  A = __SRA2(E, s1);
  B = __SRA2(G, s1);
  /* C0 = (xb - xd), C1 = (yd - yb) */
  C = __PACK2(t0, -t1);
  /* D0 = (xd - xb), D1 = (yb - yd) */
  D = __PACK2(-t0, t1);
  /* E0 = (ya+yc) - (yb+yd), E1 = (xa+xc) - (xb+xd) */
  E = __SUB2(E, G);
  /* G1 = (ya-yc) + (xb-xd), G0 = (xa-xc) - (yb-yd) */
  G = __ADD2(F, C);
  /* H1 = (ya-yc) - (xb-xd), H0 = (xa-xc) + (yb-yd) */
  H = __ADD2(F, D);
  /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
  /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
  t0 = (int16_t)(__DOTP2(CoSi2, E) >> 16U);
  t1 = (int16_t)(__DOTP2(C2, E) >> 16U);
  /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
  /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
  t2 = (int16_t)(__DOTP2(CoSi1, H) >> 16U);
  t3 = (int16_t)(__DOTP2(C1, H) >> 16U);
  /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
  /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
  t4 = (int16_t)(__DOTP2(CoSi3, G) >> 16U);
  t5 = (int16_t)(__DOTP2(C3, G) >> 16U);
  /* ya' = ya + yb + yc + yd */
  /* xa' = xa + xb + xc + xd */
  A = __ADD2(A, B);
  E = __PACK2(t1, t0);
  F = __PACK2(t3, t2);
  G = __PACK2(t5, t4);
  *((v2s *)&pOut[i0_store * 2U]) = A;
  *((v2s *)&pOut[i1_store * 2U]) = E;
  *((v2s *)&pOut[i2_store * 2U]) = F;
  *((v2s *)&pOut[i3_store * 2U]) = G;
#else
  /* Read xb (real), yb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read xa (real), ya (imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  asm volatile("pv.sra.sci.h  %[B],%[B],0x2;"
               "pv.sra.sci.h  %[D],%[D],0x2;"
               "pv.sra.sci.h  %[A],%[A],0x2;"
               "pv.sra.sci.h  %[C],%[C],0x2;"
               /* G = (xb + xd), (yb + yd) */
               /* H = (xb - xd), (yb - yd) */
               /* E = (xa + xc), (ya + yc) */
               /* F = (xa - xc), (ya - yc) */
               "pv.add.h      %[G],%[B],%[D];"
               "pv.sub.h      %[H],%[B],%[D];"
               "pv.add.h      %[E],%[A],%[C];"
               "pv.sub.h      %[F],%[A],%[C];"
               /* A = (xa + xc + xb + xd), (ya + yc + yb + yd) */
               "pv.sra.sci.h  %[A],%[E],0x1;"
               "pv.sra.sci.h  %[B],%[G],0x1;"
               "pv.add.h      %[A],%[A],%[B];"
               /* E = (xa + xc - xb - xd), (ya + yc - yb - yd) */
               "pv.sub.h      %[E],%[E],%[G];"
               /* C = (yb - yd), (xd - xb) */
               "pv.extract.h  %[C],%[H],0;"
               "pv.extract.h  %[D],%[H],1;"
               "sub           %[D],zero,%[D];"
               "pv.pack       %[C],%[C],%[D];"
               /* G = (xa - xc + yb - yd), (ya - yc + xd - xb) */
               /* H = (xa - xc + yd - yb), (ya - yc + xb - xd) */
               "pv.add.h      %[G],%[F],%[C];"
               "pv.sub.h      %[H],%[F],%[C];"
               /* E = (E * CoSi2) >> 16, (E * C2) >> 16 */
               "pv.dotsp.h    %[B],%[CoSi2],%[E];"
               "pv.dotsp.h    %[C],%[C2],%[E];"
               "srai          %[B],%[B],0x10;"
               "srai          %[C],%[C],0x10;"
               "pv.pack       %[E],%[C],%[B];"
               /* F = (H * CoSi1) >> 16, (H * C1) >> 16 */
               "pv.dotsp.h    %[B],%[CoSi1],%[H];"
               "pv.dotsp.h    %[C],%[C1],%[H];"
               "srai          %[B],%[B],0x10;"
               "srai          %[C],%[C],0x10;"
               "pv.pack       %[F],%[C],%[B];"
               /* G = (G * CoSi3) >> 16, (G * C3) >> 16 */
               "pv.dotsp.h    %[B],%[CoSi3],%[G];"
               "pv.dotsp.h    %[C],%[C3],%[G];"
               "srai          %[B],%[B],0x10;"
               "srai          %[C],%[C],0x10;"
               "pv.pack       %[G],%[C],%[B];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H)
               : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                 [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
               :);
  *((v2s *)&pOut[i0_store * 2U]) = A;
  *((v2s *)&pOut[i1_store * 2U]) = E;
  *((v2s *)&pOut[i2_store * 2U]) = F;
  *((v2s *)&pOut[i3_store * 2U]) = G;
#endif
}

/**
  @brief         Middle butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are
  interleaved
  @param[in]     i0 points to the first element to be processed
  @param[in]     n2 number of elements in the first wing of the butterfly
  @param[in]     CoSi1 packed cosine and sine first twiddle
  @param[in]     CoSi2 packed cosine and sine second twiddle
  @param[in]     CoSi3 packed cosine and sine third twiddle
  @param[in]     C1 packed sine and cosine first twiddle
  @param[in]     C2 packed sine and cosine second twiddle
  @param[in]     C3 packed sine and cosine third twiddle
  @return        none
*/
static inline void radix4_butterfly_middle(int16_t *pIn, int16_t *pOut,
                                           uint32_t i0, uint32_t n2, v2s CoSi1,
                                           v2s CoSi2, v2s CoSi3, v2s C1, v2s C2,
                                           v2s C3) {
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2s A, B, C, D, E, F, G, H;

// LOAD INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
   * 3fftLen/4] */
  i1 = i0 + NUM_BANKS;
  i2 = i1 + NUM_BANKS;
  i3 = i2 + NUM_BANKS;
#else
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
   * 3fftLen/4] */
  i1 = i0 + n2;
  i2 = i1 + n2;
  i3 = i2 + n2;
#endif
// STORE INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  uint32_t n2_store = n2 >> 2U;
  i0_store =
      (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * NUM_BANKS;
  i1_store = i0_store + n2_store;
  i2_store = i1_store + n2_store;
  i3_store = i2_store + n2_store;
#else
  i0_store = i0;
  i1_store = i1;
  i2_store = i2;
  i3_store = i3;
#endif

#ifndef ASM
  int16_t t0, t1, t2, t3, t4, t5;
  v2s s1 = {1, 1};
  /* Read yb (real), xb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read yd (real), xd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read ya (real), xa(imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read yc (real), xc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  /* G0 = (yb + yd), G1 = (xb + xd) */
  G = __ADD2(B, D);
  /* H0 = (yb - yd), H1 = (xb - xd) */
  H = __SUB2(B, D);
  /* E0 = (ya + yc), E1 = (xa + xc) */
  E = __ADD2(A, C);
  /* F0 = (ya - yc), F1 =(xa - xc) */
  F = __SUB2(A, C);
  G = __SRA2(G, s1);
  H = __SRA2(H, s1);
  E = __SRA2(E, s1);
  F = __SRA2(F, s1);
  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];
  /* C0 = (ya+yc) - (yb+yd), C1 = (xa+xc) - (xb+xd) */
  C = __SUB2(E, G);
  /* D0 = (ya+yc) + (yb+yd), D1 = (xa+xc) + (xb+xd) */
  D = __ADD2(E, G);
  /* A0 = (xb-xd), A1 = (yd-yb) */
  A = __PACK2(t0, -t1);
  /* B0 = (xd-xb), B1 = (yb-yd) */
  B = __PACK2(-t0, t1);
  /* xa' = xa + xb + xc + xd */
  /* ya' = ya + yb + yc + yd */
  D = __SRA2(D, s1);
  /* E1 = (ya-yc) + (xb-xd),  E0 = (xa-xc) - (yb-yd)) */
  E = __ADD2(F, A);
  /* F1 = (ya-yc) - (xb-xd), F0 = (xa-xc) + (yb-yd)) */
  F = __ADD2(F, B);
  /* xc' = (xa-xb+xc-xd)* co2 + (ya-yb+yc-yd)* (si2) */
  /* yc' = (ya-yb+yc-yd)* co2 - (xa-xb+xc-xd)* (si2) */
  t0 = (int16_t)(__DOTP2(CoSi2, C) >> 16U);
  t1 = (int16_t)(__DOTP2(C2, C) >> 16U);
  /* xb' = (xa+yb-xc-yd)* co1 + (ya-xb-yc+xd)* (si1) */
  /* yb' = (ya-xb-yc+xd)* co1 - (xa+yb-xc-yd)* (si1) */
  t2 = (int16_t)(__DOTP2(CoSi1, F) >> 16U);
  t3 = (int16_t)(__DOTP2(C1, F) >> 16U);
  /* xd' = (xa-yb-xc+yd)* Co3 + (ya+xb-yc-xd)* (si3) */
  /* yd' = (ya+xb-yc-xd)* Co3 - (xa-yb-xc+yd)* (si3) */
  t4 = (int16_t)(__DOTP2(CoSi3, E) >> 16U);
  t5 = (int16_t)(__DOTP2(C3, E) >> 16U);
  A = __PACK2(t1, t0);
  B = __PACK2(t3, t2);
  C = __PACK2(t5, t4);
  *((v2s *)&pOut[i0_store * 2U]) = D;
  *((v2s *)&pOut[i1_store * 2U]) = A;
  *((v2s *)&pOut[i2_store * 2U]) = B;
  *((v2s *)&pOut[i3_store * 2U]) = C;
#else
  /* Read xb (real), yb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read xa (real), ya(imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  asm volatile(/* G = (xb + xd), (yb + yd) */
               /* H = (xb - xd), (yb - yd) */
               /* E = (xa + xc), (ya + yc) */
               /* F = (xa - xc), (ya - yc) */
               "pv.add.h      %[G],%[B],%[D];"
               "pv.sub.h      %[H],%[B],%[D];"
               "pv.add.h      %[E],%[A],%[C];"
               "pv.sub.h      %[F],%[A],%[C];"
               "pv.sra.sci.h  %[G],%[G],0x1;"
               "pv.sra.sci.h  %[H],%[H],0x1;"
               "pv.sra.sci.h  %[E],%[E],0x1;"
               "pv.sra.sci.h  %[F],%[F],0x1;"
               /* C = (xa + xc - xb - xd), (ya + yc - yb - yd) */
               /* D = (xa + xc + xb + xd), (ya + yc + yb + yd) */
               "pv.sub.h      %[C],%[E],%[G];"
               "pv.add.h      %[D],%[E],%[G];"
               "pv.sra.sci.h  %[D],%[D],0x1;"
               /* A = (yb - yd), (xd - xb) */
               "pv.extract.h  %[B],%[H],0;"
               "pv.extract.h  %[A],%[H],1;"
               "sub           %[A],zero,%[A];"
               "pv.pack       %[A],%[B],%[A];"
               /* E = (xa - xc + yb - yd), (ya - yc + xd - xb) */
               /* F = (xa - xc + yd - yb), (ya - yc + xb - xd) */
               "pv.add.h      %[E],%[F],%[A];"
               "pv.sub.h      %[F],%[F],%[A];"
               /* B = (F * CoSi1) >> 16, (F * C1) >> 16 */
               "pv.dotsp.h    %[G],%[CoSi1],%[F];"
               "pv.dotsp.h    %[H],%[C1],%[F];"
               "srai          %[G],%[G],0x10;"
               "srai          %[H],%[H],0x10;"
               "pv.pack       %[B],%[H],%[G];"
               /* A = (C * CoSi2) >> 16, (C * C2) >> 16 */
               "pv.dotsp.h    %[G],%[CoSi2],%[C];"
               "pv.dotsp.h    %[H],%[C2],%[C];"
               "srai          %[G],%[G],0x10;"
               "srai          %[H],%[H],0x10;"
               "pv.pack       %[A],%[H],%[G];"
               /* C = (E * CoSi3) >> 16, (E * C3) >> 16 */
               "pv.dotsp.h    %[G],%[CoSi3],%[E];"
               "pv.dotsp.h    %[H],%[C3],%[E];"
               "srai          %[G],%[G],0x10;"
               "srai          %[H],%[H],0x10;"
               "pv.pack       %[C],%[H],%[G];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H)
               : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                 [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
               :);
  *((v2s *)&pOut[i0_store * 2U]) = D;
  *((v2s *)&pOut[i1_store * 2U]) = A;
  *((v2s *)&pOut[i2_store * 2U]) = B;
  *((v2s *)&pOut[i3_store * 2U]) = C;
#endif
}

/**
  @brief         Last butterfly stage.
  @param[in]     pIn  points to input buffer of 16b data, Re and Im parts are
  interleaved
  @param[out]    pOut  points to output buffer of 16b data, Re and Im parts are
  interleaved
  @param[in]     i0 points to the first element to be processed
  @return        none
*/
static inline void radix4_butterfly_last(int16_t *pIn, int16_t *pOut,
                                         uint32_t i0) {
  int16_t t0, t1;
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2s A, B, C, D, E, F, G, H;

// LOAD INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
      pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + NUM_BANKS;
  i2 = i1 + NUM_BANKS;
  i3 = i2 + NUM_BANKS;
#else
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
      pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + 1U;
  i2 = i1 + 1U;
  i3 = i2 + 1U;
#endif
// STORE INDEXES
#if defined(FOLDED) || (defined(SCHEDULED) && defined(BITREVERSETABLE))
  i0_store = i0 * 4;
  i1_store = i0_store + 1;
  i2_store = i1_store + 1;
  i3_store = i2_store + 1;
#else
  i0_store = i0;
  i1_store = i1;
  i2_store = i2;
  i3_store = i3;
#endif

#ifndef ASM
  v2s s1 = {1, 1};
  /* Read yb (real), xb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read yd (real), xd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read ya (real), xa(imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read yc (real), xc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  /* H0 = (yb-yd), H1 = (xb-xd) */
  H = __SUB2(B, D);
  /* G0 = (yb+yd), G1 = (xb+xd) */
  G = __ADD2(B, D);
  /* E0 = (ya+yc), E1 = (xa+xc) */
  E = __ADD2(A, C);
  /* F0 = (ya-yc), F1 = (xa-xc) */
  F = __SUB2(A, C);
  H = __SRA2(H, s1);
  G = __SRA2(G, s1);
  E = __SRA2(E, s1);
  t0 = (int16_t)H[0];
  t1 = (int16_t)H[1];
  F = __SRA2(F, s1);
  /* xa' = (xa+xb+xc+xd) */
  /* ya' = (ya+yb+yc+yd) */
  *((v2s *)&pOut[i0_store * 2U]) = __ADD2(E, G);
  /* A0 = (xb-xd), A1 = (yd-yb) */
  A = __PACK2(-t0, t1);
  /* B0 = (xd-xb), B1 = (yb-yd) */
  B = __PACK2(t0, -t1);
  /* xc' = (xa-xb+xc-xd) */
  /* yc' = (ya-yb+yc-yd) */
  E = __SUB2(E, G);
  /* xb' = (xa+yb-xc-yd) */
  /* yb' = (ya-xb-yc+xd) */
  A = __ADD2(F, A);
  /* xd' = (xa-yb-xc+yd) */
  /* yd' = (ya+xb-yc-xd) */
  B = __ADD2(F, B);
  *((v2s *)&pOut[i1_store * 2U]) = E;
  *((v2s *)&pOut[i2_store * 2U]) = A;
  *((v2s *)&pOut[i3_store * 2U]) = B;
#else
  /* Read xb (real), yb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read xa (real), ya(imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  int16_t t2, t3;
  v2s s1;
  asm volatile(
      "addi %[s1], zero, 0x01;"
      "slli %[s1], %[s1], 0x10;"
      "addi %[s1], %[s1], 0x01;"
      /* H = xb - xd, yb - yd */
      /* G = xb + xd, yb + yd */
      /* E = xa + xc, ya + yc */
      /* F = xa - xc, ya - yc */
      "pv.sub.h  %[H],%[B],%[D];"
      "pv.add.h  %[G],%[B],%[D];"
      "pv.add.h  %[E],%[A],%[C];"
      "pv.sub.h  %[F],%[A],%[C];"
      "pv.sra.h  %[H],%[H],%[s1];"
      "pv.sra.h  %[G],%[G],%[s1];"
      "pv.sra.h  %[E],%[E],%[s1];"
      /* A = yd - yb, xb - xd */
      /* B = yb - yd, xd - xb */
      "pv.extract.h  %[t0],%[H],0;"
      "pv.extract.h  %[t1],%[H],1;"
      "pv.sra.h  %[F],%[F],%[s1];"
      "sub %[t2], zero, %[t0];"
      "sub %[t3], zero, %[t1];"
      "pv.pack %[A],%[t2],%[t1];"
      "pv.pack %[B],%[t0],%[t3];"
      /* H = xa + xc + xb + xd */
      /* E = xa + xc - xb - xd */
      /* A = xa - xc + yd - yb */
      /* B = xa - xc + yb - yd */
      "pv.add.h  %[H],%[E],%[G];"
      "pv.sub.h  %[E],%[E],%[G];"
      "pv.add.h  %[A],%[F],%[A];"
      "pv.add.h  %[B],%[F],%[B];"
      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
        [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
        [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3), [s1] "=&r"(s1)
      :
      :);
  *((v2s *)&pOut[i0_store * 2U]) = H;
  *((v2s *)&pOut[i1_store * 2U]) = E;
  *((v2s *)&pOut[i2_store * 2U]) = A;
  *((v2s *)&pOut[i3_store * 2U]) = B;
#endif
}
