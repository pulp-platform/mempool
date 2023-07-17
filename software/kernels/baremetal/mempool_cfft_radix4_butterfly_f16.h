// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include "xpulp/builtins_v2.h"

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
static inline void radix4_butterfly(__fp16 *pIn, __fp16 *pOut,
                                    uint32_t i0, uint32_t n2, v2h CoSi1,
                                    v2h CoSi2, v2h CoSi3, v2h C1, v2h C2,
                                    v2h C3) {
  uint32_t i1, i2, i3;
  __fp16 t0, t1, t2, t3, t4, t5;
  v2h A, B, C, D, E, F, G, H;

#if defined(FOLDED) || defined(SCHEDULED)
  /* index calculation for the input as, */
  /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + N_BANKS;
  i2 = i1 + N_BANKS;
  i3 = i2 + N_BANKS;
  uint32_t n2_store = n2 >> 2U;
  uint32_t i0_store =
      (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * N_BANKS;
  uint32_t i1_store = i0_store + n2_store;
  uint32_t i2_store = i1_store + n2_store;
  uint32_t i3_store = i2_store + n2_store;
#else
  /* index calculation for the input as, */
  /* pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + n2;
  i2 = i1 + n2;
  i3 = i2 + n2;
#endif
  /* Read ya (real), xa (imag) input */
  A = *(v2h *)&pIn[i0 * 2U];
  /* Read yb (real), xb(imag) input */
  B = *(v2h *)&pIn[i1 * 2U];
  /* Read yc (real), xc(imag) input */
  C = *(v2h *)&pIn[i2 * 2U];
  /* Read yd (real), xd(imag) input */
  D = *(v2h *)&pIn[i3 * 2U];
  asm volatile(
               // xa + xc, ya + yc
               "vfadd.h  %[E],%[A],%[C];"
               // xa - xc, ya - yc
               "vfsub.h  %[F],%[A],%[C];"
               // xb + xd, yd + yd
               "vfadd.h  %[G],%[B],%[D];"
               // xb - xd, yb - yd
               "vfsub.h  %[H],%[B],%[D];"
               "pv.extract.h  %[t0],%[H],0;"
               "pv.extract.h  %[t1],%[H],1;"
               "fsub.h %[t3],zero,%[t1];"
               "fsub.h %[t4],zero,%[t0];"
               // yd - yb, xb - xd
               "pv.pack.h %[C],%[t0],%[t3];"
               // yb - yd, xd - xb
               "pv.pack.h %[D],%[t4],%[t1];"
               // xa + xc + xb + xd, ya + yb + yc + yd
               "vfadd.h  %[A],%[E],%[G];"
               // xa - xc + yb - yd, ya - yc + xd - xb
               "vfadd.h  %[D],%[F],%[D];"
               // xa + xc - xb - xd, ya + yc - yb - yd
               "vfsub.h  %[B],%[E],%[G];"
               // xa - xc - yb + yd, ya - yc + xb - xd
               "vfadd.h  %[C],%[F],%[C];"
               "vfdotpex.s.h  %[t0],%[CoSi1],%[D];"
               "vfdotpex.s.h  %[t2],%[CoSi2],%[B];"
               "vfdotpex.s.h  %[t4],%[CoSi3],%[C];"
               "vfdotpex.s.h  %[t1],%[C1],%[D];"
               "vfdotpex.s.h  %[t3],%[C1],%[B];"
               "vfdotpex.s.h  %[t5],%[C3],%[C];"
               "fcvt.h.s %[t0],%[t0];"
               "fcvt.h.s %[t1],%[t1];"
               "fcvt.h.s %[t2],%[t2];"
               "fcvt.h.s %[t3],%[t3];"
               "fcvt.h.s %[t4],%[t4];"
               "fcvt.h.s %[t5],%[t5];"
               "pv.pack.h %[E],%[t1],%[t0];"
               "pv.pack.h %[F],%[t3],%[t2];"
               "pv.pack.h %[G],%[t5],%[t4];"
               : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D),
                 [E] "=&r"(E), [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H),
                 [t0] "=&r"(t0), [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3),
                 [t4] "=&r"(t4), [t5] "=&r"(t5)
               : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
                 [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3)
               :);
#if defined(FOLDED) || defined(SCHEDULED)
  *((v2h *)&pOut[i0_store * 2U]) = A;
  *((v2h *)&pOut[i1_store * 2U]) = E;
  *((v2h *)&pOut[i2_store * 2U]) = F;
  *((v2h *)&pOut[i3_store * 2U]) = G;
#else
  *((v2h *)&pOut[i0 * 2U]) = A;
  *((v2h *)&pOut[i1 * 2U]) = E;
  *((v2h *)&pOut[i2 * 2U]) = F;
  *((v2h *)&pOut[i3 * 2U]) = G;
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
static inline void radix4_butterfly_last(__fp16 *pIn, __fp16 *pOut,
                                         uint32_t i0) {
  __fp16 t0, t1;
  uint32_t i1, i2, i3;
  v2h A, B, C, D, E, F, G, H;

#if defined(FOLDED) || defined(SCHEDULED)
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
      pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + N_BANKS;
  i2 = i1 + N_BANKS;
  i3 = i2 + N_BANKS;
#ifndef SCHEDULED
  uint32_t i0_store = i0 * 4;
  uint32_t i1_store = i0_store + 1;
  uint32_t i2_store = i1_store + 1;
  uint32_t i3_store = i2_store + 1;
#endif
#else
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
      pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + 1U;
  i2 = i1 + 1U;
  i3 = i2 + 1U;
#endif

  /* Read ya (real), xa(imag) input */
  A = *(v2h *)&pIn[i0 * 2U];
  /* Read yb (real), xb(imag) input */
  B = *(v2h *)&pIn[i1 * 2U];
  /* Read yc (real), xc(imag) input */
  C = *(v2h *)&pIn[i2 * 2U];
  /* Read yd (real), xd(imag) input */
  D = *(v2h *)&pIn[i3 * 2U];
  __fp16 t2, t3;
  asm volatile(
      "vfsub.h  %[H],%[B],%[D];"
      "vfadd.h  %[G],%[B],%[D];"
      "vfadd.h  %[E],%[A],%[C];"
      "vfsub.h  %[F],%[A],%[C];"
      "pv.extract.h  %[t0],%[H],0;"
      "pv.extract.h  %[t1],%[H],1;"
      "fsub.h %[t2], zero, %[t0];"
      "fsub.h %[t3], zero, %[t1];"
      "pv.pack.h %[A],%[t2],%[t1];"
      "pv.pack.h %[B],%[t0],%[t3];"
      "vfadd.h  %[H],%[E],%[G];"
      "vfsub.h  %[E],%[E],%[G];"
      "vfadd.h  %[A],%[F],%[A];"
      "vfadd.h  %[B],%[F],%[B];"
      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
        [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [t0] "=&r"(t0),
        [t1] "=&r"(t1), [t2] "=&r"(t2), [t3] "=&r"(t3)
      :
      :);
#if defined(FOLDED)
  *((v2h *)&pOut[i0_store * 2U]) = H;
  *((v2h *)&pOut[i1_store * 2U]) = E;
  *((v2h *)&pOut[i2_store * 2U]) = A;
  *((v2h *)&pOut[i3_store * 2U]) = B;
#else
  *((v2h *)&pOut[i0 * 2U]) = H;
  *((v2h *)&pOut[i1 * 2U]) = E;
  *((v2h *)&pOut[i2 * 2U]) = A;
  *((v2h *)&pOut[i3 * 2U]) = B;
#endif

}
