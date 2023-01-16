// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#pragma once

//static inline void inner_loop (int16_t* pPilotTX, int16_t* pH, uint32_t nTX, v2s ab, v2s ab_n, uint32_t i, uint32_t j) {
//  v2s cd0, cd1, cd2, cd3;
//  int32_t re0, re1, re2, re3;
//  int32_t im0, im1, im2, im3;
//  int32_t D0, D1, D2, D3;
//  int32_t S = (1 << 8U);
////    cd = *(v2s *)&pPilotTX[2U * j];
////    D = (int32_t)__DOTP2(cd, cd);
////    D = (1 << 8) / D;
////    re = (int32_t)__DOTP2(ab, cd);
////    t0 = ab[0];
////    t1 = ab[1];
////    ab_t = __PACK2(t0, -t1);
////    im = (int32_t)__DOTP2(ab_t, cd);
////    re = (re * D) >> 8U;
////    im = (im * D) >> 8U;
//    cd0 = *(v2s *)&pPilotTX[2U * j];
//    cd1 = *(v2s *)&pPilotTX[2U * (j + 1)];
//    cd2 = *(v2s *)&pPilotTX[2U * (j + 2)];
//    cd3 = *(v2s *)&pPilotTX[2U * (j + 3)];
//    asm volatile (
//        // Compute denominator
//        "pv.dotsp.h    %[D0],  %[cd0],  %[cd0];"
//        "pv.dotsp.h    %[D1],  %[cd1],  %[cd1];"
//        "pv.dotsp.h    %[D2],  %[cd2],  %[cd2];"
//        "pv.dotsp.h    %[D3],  %[cd3],  %[cd3];"
//        "div           %[D0],  %[S],    %[D0];"
//        "div           %[D1],  %[S],    %[D1];"
//        "div           %[D2],  %[S],    %[D2];"
//        "div           %[D3],  %[S],    %[D3];"
//        // Compute numerator
//        "pv.dotsp.h    %[re0], %[ab],   %[cd0];"
//        "pv.dotsp.h    %[re1], %[ab],   %[cd1];"
//        "pv.dotsp.h    %[re2], %[ab],   %[cd2];"
//        "pv.dotsp.h    %[re3], %[ab],   %[cd3];"
//        "pv.dotsp.h    %[im0], %[ab_n], %[cd0];"
//        "pv.dotsp.h    %[im1], %[ab_n], %[cd1];"
//        "pv.dotsp.h    %[im2], %[ab_n], %[cd2];"
//        "pv.dotsp.h    %[im3], %[ab_n], %[cd3];"
//        "mul           %[re0], %[re0],  %[D0];"
//        "mul           %[re1], %[re1],  %[D1];"
//        "mul           %[re2], %[re2],  %[D2];"
//        "mul           %[re3], %[re3],  %[D3];"
//        "mul           %[im0], %[im0],  %[D0];"
//        "mul           %[im1], %[im1],  %[D1];"
//        "mul           %[im2], %[im2],  %[D2];"
//        "mul           %[im3], %[im3],  %[D3];"
//        // Rescale after division
//        "srai          %[re0], %[re0],  0x8;"
//        "srai          %[im0], %[im0],  0x8;"
//        "srai          %[re1], %[re1],  0x8;"
//        "srai          %[im1], %[im1],  0x8;"
//        "srai          %[re2], %[re2],  0x8;"
//        "srai          %[im2], %[im2],  0x8;"
//        "srai          %[re3], %[re3],  0x8;"
//        "srai          %[im3], %[im3],  0x8;"
//        // Clip to 16b
//        "p.clip        %[re0], %[re0],  0x16;"
//        "p.clip        %[im0], %[im0],  0x16;"
//        "p.clip        %[re1], %[re1],  0x16;"
//        "p.clip        %[im1], %[im1],  0x16;"
//        "p.clip        %[re1], %[re1],  0x16;"
//        "p.clip        %[im1], %[im1],  0x16;"
//        "p.clip        %[re2], %[re2],  0x16;"
//        "p.clip        %[im2], %[im2],  0x16;"
//        "p.clip        %[re3], %[re3],  0x16;"
//        "p.clip        %[im3], %[im3],  0x16;"
//        // Pack in 32b word
//        "pv.pack       %[re0], %[re0], %[im0];"
//        "pv.pack       %[re1], %[re1], %[im1];"
//        "pv.pack       %[re2], %[re2], %[im2];"
//        "pv.pack       %[re3], %[re3], %[im3];"
//        : [D0] "=&r" (D0), [D1] "=&r" (D1), [D2] "=&r" (D2), [D3] "=&r" (D3),
//          [re0] "=&r" (re0), [re1] "=&r" (re1), [re2] "=&r" (re2), [re3] "=&r" (re3),
//          [im0] "=&r" (im0), [im1] "=&r" (im1), [im2] "=&r" (im2), [im3] "=&r" (im3)
//        : [cd0] "r"(cd0), [cd1] "r"(cd1), [cd2] "r"(cd2), [cd3] "r"(cd3),
//          [ab] "r" (ab), [ab_n] "r" (ab_n), [S] "r" (S)
//        :
//    );
////    *((v2s *)&pH[2*(i * nTX + j    )]) = __PACK2((int16_t) re0, (int16_t) im0);
////    *((v2s *)&pH[2*(i * nTX + j + 1)]) = __PACK2((int16_t) re1, (int16_t) im1);
////    *((v2s *)&pH[2*(i * nTX + j + 2)]) = __PACK2((int16_t) re2, (int16_t) im2);
////    *((v2s *)&pH[2*(i * nTX + j + 3)]) = __PACK2((int16_t) re3, (int16_t) im3);
//    *((v2s *)&pH[2*(i * nTX + j    )]) = (v2s) re0;
//    *((v2s *)&pH[2*(i * nTX + j + 1)]) = (v2s) re1;
//    *((v2s *)&pH[2*(i * nTX + j + 2)]) = (v2s) re2;
//    *((v2s *)&pH[2*(i * nTX + j + 3)]) = (v2s) re3;
//    //dump_x(j);
//    return;//

//}

/**
  @brief         Block-type channel estimation.
  @param[in]     pH  points to output channel
  @param[in]     pPilotRX points to received symbol
  @param[in]     pPilotTX points to sent pilot
  @param[in]     nTX Number of transmitters
  @param[in]     nRX Number of receivers
  @param[in]     nSc Number of Subcarriers
  @return        none
*/
void mempool_chest_q16p_unrolled4_xpulpv2(int16_t* volatile pH, int16_t* volatile pPilotRX, int16_t* volatile pPilotTX, uint32_t nRX, uint32_t nTX, uint32_t nSc, uint32_t core_id, uint32_t nPE) {

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  int16_t* volatile pTX;
  int16_t* volatile pRX;
  int16_t* volatile pOut;

  for(uint32_t k = core_id; k < nSc; k += nPE) {
      pTX = &(*pPilotTX) + k * (2 * nTX);
      pRX = &(*pPilotRX) + k * (2 * nRX);
      pOut  = &(*pH) + k * 2 * (nTX * nRX);
      for(uint32_t i = 0; i < nRX; i += 4) {
          ab0 = *(v2s *)&pRX[2U * i];
          ab1 = *(v2s *)&pRX[2U * (i + 1)];
          ab2 = *(v2s *)&pRX[2U * (i + 2)];
          ab3 = *(v2s *)&pRX[2U * (i + 3)];
          asm volatile (
            "pv.sub.h      %[ab_n0], %[zero], %[ab0];"
            "pv.sub.h      %[ab_n1], %[zero], %[ab1];"
            "pv.sub.h      %[ab_n2], %[zero], %[ab2];"
            "pv.sub.h      %[ab_n3], %[zero], %[ab3];"
            "pv.shuffle2.h %[ab_n0], %[ab0],  %[mask];"
            "pv.shuffle2.h %[ab_n1], %[ab1],  %[mask];"
            "pv.shuffle2.h %[ab_n2], %[ab2],  %[mask];"
            "pv.shuffle2.h %[ab_n3], %[ab3],  %[mask];"
            : [ab_n0] "=&r" (ab_n0), [ab_n1] "=&r" (ab_n1), [ab_n2] "=&r" (ab_n2), [ab_n3] "=&r" (ab_n3)
            : [ab0] "r" (ab0), [ab1] "r" (ab1), [ab2] "r" (ab2), [ab3] "r" (ab3),
              [zero] "r" ((v2s) {0,0}), [mask] "r" ((v2s) {0x1,0x2})
            :
          );
          for(uint32_t j = 0; j < nTX; j += 4) {
              inner_loop(pTX, pOut, nTX, ab0, ab_n0, i, j);
              inner_loop(pTX, pOut, nTX, ab1, ab_n1, i + 1, j);
              inner_loop(pTX, pOut, nTX, ab2, ab_n2, i + 2, j);
              inner_loop(pTX, pOut, nTX, ab3, ab_n3, i + 3, j);
          }
      }
  }
  // dump_x(core_id);
  mempool_barrier(nPE);
  return;
}

/**
  @brief         Block-type channel estimation.
  @param[in]     pH  points to output channel
  @param[in]     pPilotRX points to received symbol
  @param[in]     pPilotTX points to sent pilot
  @param[in]     nTX Number of transmitters
  @param[in]     nRX Number of receivers
  @param[in]     nSc Number of Subcarriers
  @return        none
*/
void mempool_chest_q16p2_unrolled4_xpulpv2(int16_t* volatile pH, int16_t* volatile pPilotRX, int16_t* volatile pPilotTX, uint32_t nRX, uint32_t nTX, uint32_t nSc, uint32_t core_id, uint32_t nPE) {

  v2s ab0, ab1, ab2, ab3;
  v2s ab_n0, ab_n1, ab_n2, ab_n3;
  int16_t* volatile pTX;
  int16_t* volatile pRX;
  int16_t* volatile pOut;
  for (uint32_t idx = core_id * 4; idx < (nSc * nRX * nTX); idx += 1024) {

      uint32_t k = idx / (nRX * nTX);
      uint32_t i = (idx % (nRX * nTX)) / nTX;
      uint32_t j = (idx % (nRX * nTX)) % nTX;
      pTX = &(*pPilotTX) + k * (2 * nTX);
      pRX = &(*pPilotRX) + k * (2 * nRX);
      pOut  = &(*pH) + k * 2 * (nTX * nRX);
      ab0 = *(v2s *)&pRX[2U * i];

      //dump_x(k);
      //dump_y(i);
      //dump_z(k * (nTX * nRX) + i * nTX + j);

      ab0 = *(v2s *)&pRX[2U * i];
      ab1 = *(v2s *)&pRX[2U * (i + 1)];
      ab2 = *(v2s *)&pRX[2U * (i + 2)];
      ab3 = *(v2s *)&pRX[2U * (i + 3)];
      asm volatile (
        "pv.sub.h      %[ab_n0], %[zero], %[ab0];"
        "pv.sub.h      %[ab_n1], %[zero], %[ab1];"
        "pv.sub.h      %[ab_n2], %[zero], %[ab2];"
        "pv.sub.h      %[ab_n3], %[zero], %[ab3];"
        "pv.shuffle2.h %[ab_n0], %[ab0],  %[mask];"
        "pv.shuffle2.h %[ab_n1], %[ab1],  %[mask];"
        "pv.shuffle2.h %[ab_n2], %[ab2],  %[mask];"
        "pv.shuffle2.h %[ab_n3], %[ab3],  %[mask];"
        : [ab_n0] "=&r" (ab_n0), [ab_n1] "=&r" (ab_n1), [ab_n2] "=&r" (ab_n2), [ab_n3] "=&r" (ab_n3)
        : [ab0] "r" (ab0), [ab1] "r" (ab1), [ab2] "r" (ab2), [ab3] "r" (ab3),
          [zero] "r" ((v2s) {0,0}), [mask] "r" ((v2s) {0x1,0x2})
        :
      );
      inner_loop(pTX, pOut, nTX, ab0, ab_n0, i, j);
      // inner_loop(pTX, pOut, nTX, ab1, ab_n1, i + 1, j);
      // inner_loop(pTX, pOut, nTX, ab2, ab_n2, i + 2, j);
      // inner_loop(pTX, pOut, nTX, ab3, ab_n3, i + 3, j);

  }
  //dump_x(core_id);
  mempool_log_partial_barrier(2, core_id, N_SAMPLES);
  return;

}
