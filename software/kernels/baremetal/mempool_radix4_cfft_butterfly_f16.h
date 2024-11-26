// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once
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
static inline void radix4_butterfly_first(__fp16 *pIn, __fp16 *pOut,
                                          uint32_t i0, uint32_t n2, v2h CoSi1,
                                          v2h CoSi2, v2h CoSi3, v2h C1, v2h C2,
                                          v2h C3) {
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2h A, B, C, D, E, F, G, H;

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
  i0_store = (i0 % n2_store) + (i0 / n2_store) * N_BANKS;
  i1_store = i0_store + n2_store;
  i2_store = i1_store + n2_store;
  i3_store = i2_store + n2_store;
#else
  i0_store = i0;
  i1_store = i1;
  i2_store = i2;
  i3_store = i3;
#endif

  float s0 = 0.0f;
  float s1 = 0.0f;
  float s2 = 0.0f;
  float s3 = 0.0f;
  float s4 = 0.0f;
  float s5 = 0.0f;
  /* Read xb (real), yb(imag) input */
  B = *(v2h *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2h *)&pIn[i3 * 2U];
  /* Read xa (real), ya(imag) input */
  A = *(v2h *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2h *)&pIn[i2 * 2U];

  asm volatile(
      // G = (xb + xd), (yb + yd)
      "vfadd.h  %[G],%[B],%[D];"
      // H = (xb - xd), (yb - yd)
      "vfsub.h  %[H],%[B],%[D];"
      // E = (xa + xc), (ya + yc)
      "vfadd.h  %[E],%[A],%[C];"
      // F = (xa - xc), (ya - yc)
      "vfsub.h  %[F],%[A],%[C];"

      // C = (yb - yd), (xd - xb)
      "pv.shuffle2.h %[C],%[H],%[mask];"
      "vfmul.h       %[C],%[C],%[neg_mask];"

      // xa + xb + xc + xd, ya + yc + yb + yd
      "vfadd.h  %[A],%[E],%[G];"
      // xa + xc - xb - xd, ya + yc - yb - yd
      "vfsub.h  %[B],%[E],%[G];"
      // xa - xc + yb - yd, ya - yc + xd - xb
      "vfadd.h  %[D],%[F],%[C];"
      // xa - xc + yd - yb, ya - yc + xb - xd
      "vfsub.h  %[C],%[F],%[C];"

      // s4 = Co1 * (xa - xc + yb - yd) + Si1 * (ya - yc + xd - xb)
      // s5 = -Si1 * (xa - xc + yb - yd) + Co1 * (ya - yc + xd - xb)
      "vfdotpex.s.r.h  %[s0],%[CoSi1],%[D];"
      "vfdotpex.s.r.h  %[s1],%[C1],%[D];"
      // s0 = Co2 * (xa + xc - xb - xd) + Si2 * (ya + yc - yb - yd)
      // s1 = -Si2 * (xa + xc - xb - xd) + Co2 * (ya + yc - yb - yd)
      "vfdotpex.s.r.h  %[s2],%[CoSi2],%[B];"
      "vfdotpex.s.r.h  %[s3],%[C2],%[B];"
      // s3 = Co3 * (xa - xc + yd - yb) + Si3 * (ya - yc + xb - xd)
      // s4 = -Si3 * (xa - xc + yd - yb) + Co3 * (ya - yc + xb - xd)
      "vfdotpex.s.r.h  %[s4],%[CoSi3],%[C];"
      "vfdotpex.s.r.h  %[s5],%[C3],%[C];"
      // xb', yb'
      "vfcpka.h.s %[D], %[s1], %[s0];"
      // xc', yc'
      "vfcpka.h.s %[B], %[s3], %[s2];"
      // xd', yd'
      "vfcpka.h.s %[C], %[s5], %[s4];"
      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
        [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [s0] "=&r"(s0),
        [s1] "=&r"(s1), [s2] "=&r"(s2), [s3] "=&r"(s3), [s4] "=&r"(s4),
        [s5] "=&r"(s5)
      : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
        [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3), [mask] "r"(0x00020003),
        [neg_mask] "r"(0x3C00BC00)
      :);
  *((v2h *)&pOut[i0_store * 2U]) = A;
  *((v2h *)&pOut[i1_store * 2U]) = B;
  *((v2h *)&pOut[i2_store * 2U]) = D;
  *((v2h *)&pOut[i3_store * 2U]) = C;
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
static inline void radix4_butterfly_middle(__fp16 *pIn, __fp16 *pOut,
                                           uint32_t i0, uint32_t n2, v2h CoSi1,
                                           v2h CoSi2, v2h CoSi3, v2h C1, v2h C2,
                                           v2h C3) {
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2h A, B, C, D, E, F, G, H;

// LOAD INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4], pIn[i0 + fftLen/2], pIn[i0 +
   * 3fftLen/4] */
  i1 = i0 + N_BANKS;
  i2 = i1 + N_BANKS;
  i3 = i2 + N_BANKS;
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
      (i0 % n2_store) + (i0 / n2) * n2 + ((i0 % n2) / n2_store) * N_BANKS;
  i1_store = i0_store + n2_store;
  i2_store = i1_store + n2_store;
  i3_store = i2_store + n2_store;
#else
  i0_store = i0;
  i1_store = i1;
  i2_store = i2;
  i3_store = i3;
#endif

  float s0 = 0.0f;
  float s1 = 0.0f;
  float s2 = 0.0f;
  float s3 = 0.0f;
  float s4 = 0.0f;
  float s5 = 0.0f;
  /* Read xb (real), yb(imag) input */
  B = *(v2h *)&pIn[i1 * 2U];
  /* Read xd (real), yd(imag) input */
  D = *(v2h *)&pIn[i3 * 2U];
  /* Read xa (real), ya(imag) input */
  A = *(v2h *)&pIn[i0 * 2U];
  /* Read xc (real), yc(imag) input */
  C = *(v2h *)&pIn[i2 * 2U];

  asm volatile(
      // G = (xb + xd), (yb + yd)
      "vfadd.h  %[G],%[B],%[D];"
      // H = (xb - xd), (yb - yd)
      "vfsub.h  %[H],%[B],%[D];"
      // E = (xa + xc), (ya + yc)
      "vfadd.h  %[E],%[A],%[C];"
      // F = (xa - xc), (ya - yc)
      "vfsub.h  %[F],%[A],%[C];"

      // C = (yb - yd), (xd - xb)
      "pv.shuffle2.h %[C],%[H],%[mask];"
      "vfmul.h       %[C],%[C],%[neg_mask];"

      // xa + xb + xc + xd, ya + yc + yb + yd
      "vfadd.h  %[A],%[E],%[G];"
      // xa + xc - xb - xd, ya + yc - yb - yd
      "vfsub.h  %[B],%[E],%[G];"
      // xa - xc + yb - yd, ya - yc + xd - xb
      "vfadd.h  %[D],%[F],%[C];"
      // xa - xc + yd - yb, ya - yc + xb - xd
      "vfsub.h  %[C],%[F],%[C];"

      // s4 = Co1 * (xa - xc + yb - yd) + Si1 * (ya - yc + xd - xb)
      // s5 = -Si1 * (xa - xc + yb - yd) + Co1 * (ya - yc + xd - xb)
      "vfdotpex.s.r.h  %[s0],%[CoSi1],%[D];"
      "vfdotpex.s.r.h  %[s1],%[C1],%[D];"

      // s0 = Co2 * (xa + xc - xb - xd) + Si2 * (ya + yc - yb - yd)
      // s1 = -Si2 * (xa + xc - xb - xd) + Co2 * (ya + yc - yb - yd)
      "vfdotpex.s.r.h  %[s2],%[CoSi2],%[B];"
      "vfdotpex.s.r.h  %[s3],%[C2],%[B];"

      // s3 = Co3 * (xa - xc + yd - yb) + Si3 * (ya - yc + xb - xd)
      // s4 = -Si3 * (xa - xc + yd - yb) + Co3 * (ya - yc + xb - xd)
      "vfdotpex.s.r.h  %[s4],%[CoSi3],%[C];"
      "vfdotpex.s.r.h  %[s5],%[C3],%[C];"

      // xb', yb'
      "vfcpka.h.s %[B], %[s1], %[s0];"
      // xc', yc'
      "vfcpka.h.s %[C], %[s3], %[s2];"
      // xd', yd'
      "vfcpka.h.s %[D], %[s5], %[s4];"
      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "=&r"(E),
        [F] "=&r"(F), [G] "=&r"(G), [H] "=&r"(H), [s0] "=&r"(s0),
        [s1] "=&r"(s1), [s2] "=&r"(s2), [s3] "=&r"(s3), [s4] "=&r"(s4),
        [s5] "=&r"(s5)
      : [C1] "r"(C1), [C2] "r"(C2), [C3] "r"(C3), [CoSi1] "r"(CoSi1),
        [CoSi2] "r"(CoSi2), [CoSi3] "r"(CoSi3), [mask] "r"(0x00020003),
        [neg_mask] "r"(0x3C00BC00)
      :);
  *((v2h *)&pOut[i0_store * 2U]) = A;
  *((v2h *)&pOut[i1_store * 2U]) = C;
  *((v2h *)&pOut[i2_store * 2U]) = B;
  *((v2h *)&pOut[i3_store * 2U]) = D;
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
  __fp16 t0, t1, t2, t3;
  uint32_t i1, i2, i3;
  uint32_t i0_store, i1_store, i2_store, i3_store;
  v2h A, B, C, D, E, F, G, H;

// LOAD INDEXES
#if defined(FOLDED) || defined(SCHEDULED)
  /*  index calculation for the input as, */
  /*  pIn[i0 + 0], pIn[i0 + fftLen/4],
      pIn[i0 + fftLen/2], pIn[i0 + 3fftLen/4] */
  i1 = i0 + N_BANKS;
  i2 = i1 + N_BANKS;
  i3 = i2 + N_BANKS;
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

  /* Read xb (imag), yb(real) input */
  B = *(v2h *)&pIn[i1 * 2U];
  /* Read xd (imag), yd(real) input */
  D = *(v2h *)&pIn[i3 * 2U];
  /* Read xa (imag), ya(real) input */
  A = *(v2h *)&pIn[i0 * 2U];
  /* Read xc (imag), yc(real) input */
  C = *(v2h *)&pIn[i2 * 2U];
  asm volatile(
      /* (xb - xd), (yb - yd) */
      "vfsub.h  %[H],%[B],%[D];"
      /* (xb + xd), (yb + yd) */
      "vfadd.h  %[G],%[B],%[D];"
      /* (xa + xc), (ya + yc) */
      "vfadd.h  %[E],%[A],%[C];"
      /* (xa - xc), (ya - yc) */
      "vfsub.h  %[F],%[A],%[C];"

      /* (yd - yb), (xb - xd) */
      "pv.shuffle2.h %[A],%[H],%[mask];"
      "vfmul.h       %[A],%[A],%[neg_mask];"

      /* (xa + xc + xb + xd), (ya + yc + yb + yd) */
      "vfadd.h  %[H],%[E],%[G];"
      /* (xa + xc - xb - xd), (ya + yc - yb - yd) */
      "vfsub.h  %[E],%[E],%[G];"
      /* (xa - xc + yd - yb), (ya - yc + xb - xd) */
      "vfadd.h  %[B],%[F],%[A];"
      /* (xa - xc + yb - yd), (ya - yc + xd - xb) */
      "vfsub.h  %[A],%[F],%[A];"

      : [A] "+&r"(A), [B] "+&r"(B), [C] "+&r"(C), [D] "+&r"(D), [E] "+&r"(E),
        [F] "+&r"(F), [G] "+&r"(G), [H] "+&r"(H), [t0] "+&r"(t0),
        [t1] "+&r"(t1), [t2] "+&r"(t2), [t3] "+&r"(t3)
      : [mask] "r"(0x00020003), [neg_mask] "r"(0x3C00BC00)
      :);
  *((v2h *)&pOut[i0_store * 2U]) = H;
  *((v2h *)&pOut[i1_store * 2U]) = E;
  *((v2h *)&pOut[i2_store * 2U]) = B;
  *((v2h *)&pOut[i3_store * 2U]) = A;
}
