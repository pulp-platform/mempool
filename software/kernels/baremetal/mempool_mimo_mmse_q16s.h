// Copyright 2021 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich
// Author: Aofeng Aoshen, ETH Zurich

/** VECTORIZED CODE
  @brief         Computes the Hermitian matrix G = (H'*H + pS^2I).
  @param[in]     pH     points to input matrix
  @param[in]     pG     points to output matrix
  @param[in]     pS     points to the noise vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @param[in]     folded controls if output is folded
  @param[in]     zf     controls if the zero forcing is used
  @return        none
*/
void mempool_hermitian_q16vecs(v2s *pH, v2s *pG, v2s *pS, const uint32_t n_rx,
                               const uint32_t n_tx) {

  uint32_t i, j, k;
  v2s ab;
  v2s cd0, cd1, cd2, cd3;
  int32_t as0, as1, as2, as3;
  int32_t bs0, bs1, bs2, bs3;
  const uint32_t shuffle_mask = 0x00020003;

  for (i = 0; i < n_tx; i++) {
    j = 0;
    do {
      // Initialize the real part of sums
      as0 = 0;
      as1 = 0;
      as2 = 0;
      as3 = 0;
      // Initialize the imag part of sums
      bs0 = 0;
      bs1 = 0;
      bs2 = 0;
      bs3 = 0;
      // Inner Loop
      for (k = 0; k < n_rx; k++) {
        // inputs from matrix H_h
        ab = pH[k * n_tx + i];
        // inputs from matrix H
        cd0 = pH[k * n_tx + j];
        cd1 = pH[k * n_tx + j + 1U];
        cd2 = pH[k * n_tx + j + 2U];
        cd3 = pH[k * n_tx + j + 3U];

        // dotproducts (ac + bd) + j (ad - bc)
        asm volatile(
            // a * c + b * d
            "pv.dotsp.h  %[as0], %[ab], %[cd0];"
            "pv.dotsp.h  %[as1], %[ab], %[cd1];"
            "pv.dotsp.h  %[as2], %[ab], %[cd2];"
            "pv.dotsp.h  %[as3], %[ab], %[cd3];"
            //
            "pv.shuffle2.h  %[cd0], %[cd0], %[shuffle_mask];"
            "pv.shuffle2.h  %[cd1], %[cd1], %[shuffle_mask];"
            "pv.shuffle2.h  %[cd2], %[cd2], %[shuffle_mask];"
            "pv.shuffle2.h  %[cd3], %[cd3], %[shuffle_mask];"
            //
            "pv.sub.h %[cd0], %[zero], %[cd0];"
            "pv.sub.h %[cd1], %[zero], %[cd1];"
            "pv.sub.h %[cd2], %[zero], %[cd2];"
            "pv.sub.h %[cd3], %[zero], %[cd3];"
            // a * d - b * c
            "pv.dotsp.h  %[bs0], %[ab], %[cd0];"
            "pv.dotsp.h  %[bs1], %[ab], %[cd1];"
            "pv.dotsp.h  %[bs2], %[ab], %[cd2];"
            "pv.dotsp.h  %[bs3], %[ab], %[cd3];"
            // Rescale after multiplication
            "srai          %[as0], %[as0],  0x8;"
            "srai          %[as1], %[as1],  0x8;"
            "srai          %[as2], %[as2],  0x8;"
            "srai          %[as3], %[as3],  0x8;"
            "srai          %[bs0], %[bs0],  0x8;"
            "srai          %[bs1], %[bs1],  0x8;"
            "srai          %[bs2], %[bs2],  0x8;"
            "srai          %[bs3], %[bs3],  0x8;"
            // Clip to 16b
            "p.clip        %[as0], %[as0],  0x16;"
            "p.clip        %[as1], %[as1],  0x16;"
            "p.clip        %[as2], %[as2],  0x16;"
            "p.clip        %[as3], %[as3],  0x16;"
            "p.clip        %[bs0], %[bs0],  0x16;"
            "p.clip        %[bs1], %[bs1],  0x16;"
            "p.clip        %[bs2], %[bs2],  0x16;"
            "p.clip        %[bs3], %[bs3],  0x16;"
            : [cd0] "+&r"(cd0), [cd1] "+&r"(cd1), [cd2] "+&r"(cd2),
              [cd3] "+&r"(cd3), [as0] "+&r"(as0), [as1] "+&r"(as1),
              [as2] "+&r"(as2), [as3] "+&r"(as3), [bs0] "+&r"(bs0),
              [bs1] "+&r"(bs1), [bs2] "+&r"(bs2), [bs3] "+&r"(bs3)
            : [ab] "r"(ab), [shuffle_mask] "r"(shuffle_mask),
              [zero] "r"((v2s){0, 0})
            :);
      }
      // Compute diagonal elements
      if (i == j) {
        asm volatile("add  %[as0], %[as0], %[pS];"
                     : [as0] "+&r"(as0)
                     : [pS] "r"(pS[2 * i])
                     :);
        bs0 = 0;
      } else if (i == (j + 1U)) {
        asm volatile("add  %[as1], %[as1], %[pS];"
                     : [as1] "+&r"(as1)
                     : [pS] "r"(pS[2 * i])
                     :);
        bs1 = 0;
      } else if (i == (j + 2U)) {
        asm volatile("add  %[as2], %[as2], %[pS];"
                     : [as2] "+&r"(as2)
                     : [pS] "r"(pS[2 * i])
                     :);
        bs2 = 0;
      } else if (i == (j + 3U)) {
        asm volatile("add  %[as3], %[as3], %[pS];"
                     : [as3] "+&r"(as3)
                     : [pS] "r"(pS[2 * i])
                     :);
        bs3 = 0;
      }
      // Store
      v2s res0, res1, res2, res3;
      asm volatile(
          "pv.pack %[res0], %[as0], %[bs0];"
          "pv.pack %[res1], %[as1], %[bs1];"
          "pv.pack %[res2], %[as2], %[bs2];"
          "pv.pack %[res3], %[as3], %[bs3];"
          : [res0] "=&r"(res0), [res1] "=&r"(res1), [res2] "=&r"(res2),
            [res3] "=&r"(res3)
          : [as0] "r"(as0), [as1] "r"(as1), [as2] "r"(as2), [as3] "r"(as3),
            [bs0] "r"(bs0), [bs1] "r"(bs1), [bs2] "r"(bs2), [bs3] "r"(bs3)
          :);

      pG[(i * n_tx + j)] = res0;
      pG[(i * n_tx + j + 1U)] = res1;
      pG[(i * n_tx + j + 2U)] = res2;
      pG[(i * n_tx + j + 3U)] = res3;
      j += 4;
    } while (j < n_tx);
  }
  return;
}

/** VECTORIZED CODE
  @brief         Computes the matrix-vector product y = H' * x.
  @param[in]     pH     points to input matrix
  @param[in]     px     points to input vector
  @param[in]     py     points to output vector
  @param[in]     nrx    number of received samples
  @param[in]     ntx    number of transmitted samples
  @param[in]     folded controls if output is folded
  @return        none
*/
void mempool_MVP_conjtransp_q16vecs(v2s *pH, v2s *px, v2s *py,
                                    const uint32_t n_rx, const uint32_t n_tx,
                                    const uint32_t folded) {

  uint32_t i, j;
  int32_t as0, as1, as2, as3;
  int32_t bs0, bs1, bs2, bs3;
  int32_t ndc = 0;
  v2s ab0, ab1, ab2, ab3;
  v2s cd;
  const uint32_t shuffle_mask = 0x00020003;

  i = 0;
  do {
    // Initialize the real part of sums
    as0 = 0;
    as1 = 0;
    as2 = 0;
    as3 = 0;
    // Initialize the imag part of sums
    bs0 = 0;
    bs1 = 0;
    bs2 = 0;
    bs3 = 0;
    for (j = 0; j < n_rx; j++) {
      // inputs from matrix H_h
      ab0 = pH[j * n_tx + i];
      ab1 = pH[j * n_tx + i + 1U];
      ab2 = pH[j * n_tx + i + 2U];
      ab3 = pH[j * n_tx + i + 3U];

      // inputs from b
      cd = px[j];

      // dotproducts (ac + bd) + j (ad - bc)
      asm volatile(
          // a * c + b * d
          "pv.dotsp.h  %[as0], %[ab0], %[cd];"
          "pv.dotsp.h  %[as1], %[ab1], %[cd];"
          "pv.dotsp.h  %[as2], %[ab2], %[cd];"
          "pv.dotsp.h  %[as3], %[ab3], %[cd];"
          //
          "pv.shuffle2.h  %[ndc], %[cd], %[shuffle_mask];"
          "pv.sub.h       %[ndc], %[zero], %[ndc];"
          // a * d - b * c
          "pv.dotsp.h  %[bs0], %[ab0], %[ndc];"
          "pv.dotsp.h  %[bs1], %[ab1], %[ndc];"
          "pv.dotsp.h  %[bs2], %[ab2], %[ndc];"
          "pv.dotsp.h  %[bs3], %[ab3], %[ndc];"
          // Rescale after multiplication
          "srai          %[as0], %[as0],  0x8;"
          "srai          %[as1], %[as1],  0x8;"
          "srai          %[as2], %[as2],  0x8;"
          "srai          %[as3], %[as3],  0x8;"
          "srai          %[bs0], %[bs0],  0x8;"
          "srai          %[bs1], %[bs1],  0x8;"
          "srai          %[bs2], %[bs2],  0x8;"
          "srai          %[bs3], %[bs3],  0x8;"
          // Clip to 16b
          "p.clip        %[as0], %[as0],  0x16;"
          "p.clip        %[as1], %[as1],  0x16;"
          "p.clip        %[as2], %[as2],  0x16;"
          "p.clip        %[as3], %[as3],  0x16;"
          "p.clip        %[bs0], %[bs0],  0x16;"
          "p.clip        %[bs1], %[bs1],  0x16;"
          "p.clip        %[bs2], %[bs2],  0x16;"
          "p.clip        %[bs3], %[bs3],  0x16;"
          : [as0] "+&r"(as0), [as1] "+&r"(as1), [as2] "+&r"(as2),
            [as3] "+&r"(as3), [bs0] "+&r"(bs0), [bs1] "+&r"(bs1),
            [bs2] "+&r"(bs2), [bs3] "+&r"(bs3), [ndc] "+&r"(ndc)
          : [cd] "r"(cd), [shuffle_mask] "r"(shuffle_mask), [ab0] "r"(ab0),
            [ab1] "r"(ab1), [ab2] "r"(ab2), [ab3] "r"(ab3),
            [zero] "r"((v2s){0, 0})
          :);
    }
    if (!folded) {
      v2s res0, res1, res2, res3;
      asm volatile(
          "pv.pack %[res0], %[as0], %[bs0];"
          "pv.pack %[res1], %[as1], %[bs1];"
          "pv.pack %[res2], %[as2], %[bs2];"
          "pv.pack %[res3], %[as3], %[bs3];"
          : [res0] "=&r"(res0), [res1] "=&r"(res1), [res2] "=&r"(res2),
            [res3] "=&r"(res3)
          : [as0] "r"(as0), [as1] "r"(as1), [as2] "r"(as2), [as3] "r"(as3),
            [bs0] "r"(bs0), [bs1] "r"(bs1), [bs2] "r"(bs2), [bs3] "r"(bs3)
          :);
      // Store
      py[i] = res0;
      py[i + 1U] = res1;
      py[i + 2U] = res2;
      py[i + 3U] = res3;
      i += 4;
    }

  } while (i < n_tx);
  return;
}
