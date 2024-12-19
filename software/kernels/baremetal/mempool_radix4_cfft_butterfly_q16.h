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
  int16_t t0, t1, t2, t3, t4, t5;
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
  v2s s1, s2;
  /* Read xb (real), yb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read xa (real), ya (imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  asm volatile("addi %[s1], zero, 0x01;"
               "slli %[s1], %[s1], 0x10;"
               "addi %[s1], %[s1], 0x01;"
               "addi %[s2], zero, 0x02;"
               "slli %[s2], %[s2], 0x10;"
               "addi %[s2], %[s2], 0x02;"
               "pv.sra.h  %[B],%[B],%[s2];"
               "pv.sra.h  %[D],%[D],%[s2];"
               "pv.sra.h  %[A],%[A],%[s2];"
               "pv.sra.h  %[C],%[C],%[s2];"
               /* G = (xb + xd), (yb + yd) */
               /* H = (xb - xd), (yb - yd) */
               /* E = (xa + xc), (ya + yc) */
               /* F = (xa - xc), (ya - yc) */
               "pv.add.h  %[G],%[B],%[D];"
               "pv.sub.h  %[H],%[B],%[D];"
               "pv.add.h  %[E],%[A],%[C];"
               "pv.sub.h  %[F],%[A],%[C];"
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "pv.sra.h  %[A],%[E],%[s1];"
               "pv.sra.h  %[B],%[G],%[s1];"
               "sub %[t3],zero,%[t1];"
               "sub %[t4],zero,%[t0];"
               /* C = (yb - yd), (xd - xb) */
               /* D = (yd - yb), (xb - xd) */
               "pv.pack %[C],%[t0],%[t3];"
               "pv.pack %[D],%[t4],%[t1];"
               /* E = (xa + xc - xb - xd), (ya + yc - yb - yd) */
               /* G = (xa - xc + yb - yd), (ya - yc + xd - xb) */
               /* H = (xa - xc + yd - yb), (ya - yc + xb - xd) */
               /* A = (xa + xc + xb + xd), (ya + yc + yb + yd) */
               "pv.sub.h  %[E],%[E],%[G];"
               "pv.add.h  %[G],%[F],%[C];"
               "pv.add.h  %[H],%[F],%[D];"
               /* t0 = Co2 * (xa + xc - xb - xd) + Si2 * (ya + yc - yb - yd) */
               /* t1 = Si2 * (xa + xc - xb - xd) - Co2 * (ya + yc - yb - yd) */
               /* t2 = Co1 * (xa - xc + yd - yb) + Si2 * (ya - yc + xb - xd) */
               /* t3 = Si1 * (xa - xc + yd - yb) - Co2 * (ya - yc + xb - xd) */
               /* t4 = Co3 * (xa - xc + yb - yd) + Si3 * (ya - yc + xd - xb) */
               /* t5 = Si3 * (xa - xc + yb - yd) - Co3 * (ya - yc + xd - xb) */
               "pv.dotsp.h  %[C],%[CoSi2],%[E];"
               "pv.dotsp.h  %[D],%[C2],%[E];"
               "pv.dotsp.h  %[E],%[CoSi1],%[H];"
               "pv.dotsp.h  %[F],%[C1],%[H];"
               "srai  %[t0],%[C],0x10;"
               "srai  %[t1],%[D],0x10;"
               "pv.dotsp.h  %[C],%[CoSi3],%[G];"
               "pv.dotsp.h  %[D],%[C3],%[G];"
               "srai  %[t2],%[E],0x10;"
               "srai  %[t3],%[F],0x10;"
               "srai  %[t4],%[C],0x10;"
               "srai  %[t5],%[D],0x10;"
               "pv.add.h  %[A],%[A],%[B];"
               "pv.pack %[E],%[t1],%[t0];"
               "pv.pack %[F],%[t3],%[t2];"
               "pv.pack %[G],%[t5],%[t4];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                 [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                 [t4] "=&r"(t4), [t5] "=&r"(t5), [s1] "=&r"(s1), [s2] "=&r"(s2)
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
  int16_t t0, t1, t2, t3, t4, t5;
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
  v2s s1;
  /* Read xb (real), yb(imag) input */
  B = *(v2s *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2s *)&pIn[i3 * 2U];
  /* Read xa (real), ya(imag) input */
  A = *(v2s *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2s *)&pIn[i2 * 2U];
  asm volatile("addi %[s1], zero, 0x01;"
               "slli %[s1], %[s1], 0x10;"
               "addi %[s1], %[s1], 0x01;"
               /* G = (xb + xd), (yb + yd) */
               /* H = (xb - xd), (yb - yd) */
               /* E = (xa + xc), (ya + yc) */
               /* F = (xa - xc), (ya - yc) */
               "pv.add.h  %[G],%[B],%[D];"
               "pv.sub.h  %[H],%[B],%[D];"
               "pv.add.h  %[E],%[A],%[C];"
               "pv.sub.h  %[F],%[A],%[C];"
               "pv.sra.h  %[G],%[G],%[s1];"
               "pv.sra.h  %[H],%[H],%[s1];"
               "pv.sra.h  %[E],%[E],%[s1];"
               "pv.sra.h  %[F],%[F],%[s1];"
               /* A = (yb - yd), (xd - xb) */
               /* B = (yd - yb), (xb - xd) */
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "pv.sub.h  %[C],%[E],%[G];"
               "pv.add.h  %[D],%[E],%[G];"
               "sub %[t4],zero,%[t1];"
               "sub %[t3],zero,%[t0];"
               "pv.pack %[A],%[t0],%[t4];"
               "pv.pack %[B],%[t3],%[t1];"
               "pv.sra.h  %[D],%[D],%[s1];"
               "pv.add.h  %[E],%[F],%[A];"
               "pv.add.h  %[F],%[F],%[B];"
               /* C = (xa + xc - xb - xd), (ya + yc - yb - yd) */
               /* D = (xa + xc + xb + xd), (ya + yc + yb + yd) */
               /* E = (xa - xc + yb - yd), (ya - yc + xd - xb) */
               /* F = (xa - xc + yd - yb), (ya - yc + xb - xd) */
               "pv.dotsp.h  %[G],%[CoSi2],%[C];"
               "pv.dotsp.h  %[H],%[C2],%[C];"
               "pv.dotsp.h  %[A],%[CoSi1],%[F];"
               "pv.dotsp.h  %[B],%[C1],%[F];"
               "srai  %[t0],%[G],0x10;"
               "srai  %[t1],%[H],0x10;"
               "pv.dotsp.h  %[G],%[CoSi3],%[E];"
               "pv.dotsp.h  %[H],%[C3],%[E];"
               "srai  %[t2],%[A],0x10;"
               "srai  %[t3],%[B],0x10;"
               "srai  %[t4],%[G],0x10;"
               "srai  %[t5],%[H],0x10;"
               "pv.pack %[A],%[t1],%[t0];"
               "pv.pack %[B],%[t3],%[t2];"
               "pv.pack %[C],%[t5],%[t4];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                 [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                 [t4] "=&r"(t4), [t5] "=&r"(t5), [s1] "=&r"(s1)
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
