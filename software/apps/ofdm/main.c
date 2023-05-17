// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"
#include "xpulp/builtins_v2.h"

#include "data_ofdm.h"

dump(res1, 1);
dump(res2, 1);

#define TEST_4096
#define LOG2 (12)

#define N_FFTs_ROW 4
#define N_FFTs_COL 4
#define N_FFTs (N_FFTs_ROW * N_FFTs_COL)
#define N_BANKS (NUM_CORES * 4)

#define STEP 4
#define WU_STRIDE 1
#define DMA_NONBLOCKING


#include "tables/mempool_radix4_cfft_q16_BitRevIndexTable.h"
#include "tables/mempool_radix4_cfft_q16_twiddleCoef.h"

#include "kernel/mempool_radix4_cfft_butterfly_q16.h"
#include "kernel/mempool_radix4_cfft_q16p.h"

// Each FFT occupies 4 memory rows, each memory rows has 2*banks 16bit elements
int16_t l1_pFFT_src[4 * N_FFTs_ROW * (2 * N_BANKS)]
    __attribute__((aligned(2 * N_BANKS), section(".l1")));
int16_t l1_pFFT_dst[4 * N_FFTs_ROW * (2 * N_BANKS)]
    __attribute__((aligned(2 * N_BANKS), section(".l1")));
int16_t l1_pTw_src[3 * (2 * N_BANKS)]
    __attribute__((aligned(2 * N_BANKS), section(".l1")));
int16_t l1_pTw_dst[3 * (2 * N_BANKS)]
    __attribute__((aligned(2 * N_BANKS), section(".l1")));

int16_t l1_pBF_coef[2 * N_BEAMS * N_FFTs]
    __attribute__((section(".l1")));
int16_t l1_pBF_dst[(2 * N_BEAMS * N_SC)]
    __attribute__((aligned(2 * N_BANKS), section(".l1")));


void mempool_beamforming_2x4_i32p(const int32_t *__restrict__ pSrcA,
                              const int32_t *__restrict__ pSrcB,
                              int32_t *__restrict__ pDstC,
                              uint32_t M, uint32_t N,
                              uint32_t P, uint32_t core_id,
                              uint32_t numThreads);

int main() {

  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  mempool_start_benchmark();
  /* PHASE1 */
  // Load the first N_FFTs vectors for the FFT
  // Load the twiddles
  // Load the beamforming coefficients
  if (core_id == 0) {
    dma_memcpy_blocking((int32_t*)l1_pFFT_src, (int32_t*)l2_pFFT_src, (N_SC * N_FFTs) * sizeof(int32_t));
    dma_memcpy_blocking((int32_t*)l1_pTw_src, (int32_t*)l2_pTw_coef, (3 * N_BANKS) * sizeof(int32_t));
    dma_memcpy_blocking((int32_t*)l1_pBF_coef, (int32_t*)l2_pBF_coef, (N_BEAMS * N_FFTs) * sizeof(int32_t));
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();

  for (uint32_t round = 0; round < (N_RX / N_FFTs); ++round) {
    /* PHASE2 */
    mempool_start_benchmark();
    // Compute the N_FFTs on N_FFTs_ROW and N_FFTs_COL
    uint32_t LenFFT = N_SC;
    uint32_t offset = (LenFFT >> 2U);
    uint32_t nPE_FFT = (LenFFT >> 4U);
    if (core_id < N_FFTs_COL * nPE_FFT) {
        uint32_t col_id = core_id / nPE_FFT;
        mempool_radix4_cfft_q16p_scheduler(
            col_id, l1_pFFT_src + 2 * col_id * offset,
            l1_pFFT_dst + 2 * col_id * offset, LenFFT,
            l1_pTw_src + 2 * col_id * offset,
            l1_pTw_dst + 2 * col_id * offset, BitRevIndexTable_fixed,
            BITREVINDEXTABLE_FIXED_TABLE_LENGTH, 1, nPE_FFT);
    }
    mempool_log_barrier(2, core_id);
#ifdef DMA_NONBLOCKING
    /* PHASE3 */
    // Non-blocking transfer of the next N_FFTs vectors for the FFT
    if (core_id == 0) {
        dma_memcpy_nonblocking((int32_t*)l1_pFFT_dst, (int32_t*)l2_pFFT_src, (N_SC * N_FFTs) * sizeof(int32_t));
        dma_memcpy_nonblocking((int32_t*)l1_pTw_src, (int32_t*)l2_pTw_coef, (3 * N_BANKS) * sizeof(int32_t));
    }
#endif
    mempool_stop_benchmark();
    /* PHASE4 */
    mempool_start_benchmark();
    // Computation of Beamforming for N_FFTs_ROWs x N_FFTs_COLs in l2_pBF_dst
    // (accumulation)
    mempool_beamforming_2x4_i32p((int32_t*)l1_pBF_coef, (int32_t*)l1_pFFT_src, (int32_t*)l1_pBF_dst, N_BEAMS, N_FFTs, N_SC, core_id, num_cores);
    mempool_log_barrier(2, core_id);
    dump_res1(round);
    if (round < ((N_RX / N_FFTs) - 1)) {
#ifdef DMA_NONBLOCKING
      // Wait for the end of the dma transfer
      dma_wait();
      mempool_stop_benchmark();
#else
      mempool_stop_benchmark();
      // Blocking transfer of the next N_FFTs vectors for the following
      mempool_start_benchmark();
      if (core_id == 0) {
        dma_memcpy_blocking((int32_t*)l1_pFFT_src, (int32_t*)l2_pFFT_src, (N_SC * N_FFTs) * sizeof(int32_t));
        dma_memcpy_blocking((int32_t*)l1_pTw_src, (int32_t*)l2_pTw_coef, (3 * (N_BANKS)) * sizeof(int32_t));
      }
      mempool_log_barrier(2, core_id);
      mempool_stop_benchmark();
#endif
    }
  }
  mempool_barrier(num_cores);

  return 0;
}

void mempool_beamforming_2x4_i32p(const int32_t *__restrict__ pSrcA,
                              const int32_t *__restrict__ pSrcB,
                              int32_t *__restrict__ pDstC,
                              uint32_t M, uint32_t N,
                              uint32_t P, uint32_t core_id,
                              uint32_t numThreads) {
  uint32_t i = 0; // loop counter for M
  uint32_t j = 0; // loop counter for N
  uint32_t k = 0; // loop counter for P

  uint32_t shift_id = core_id % (M / 2);
  for (k = core_id * 4; k < P; k += 4 * numThreads) {
    for (i = 2 * shift_id; i < M; i += 2) {
      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum02 = 0;
      int32_t sum03 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum12 = 0;
      int32_t sum13 = 0;
      for (j = 0; j < N; j += 2) {
        int32_t a00 = pSrcA[(i + 0) * N + (j + 0)];
        int32_t a01 = pSrcA[(i + 0) * N + (j + 1)];
        int32_t a10 = pSrcA[(i + 1) * N + (j + 0)];
        int32_t a11 = pSrcA[(i + 1) * N + (j + 1)];
        int32_t b00 = pSrcB[(j + 0) * P + (k + 0)];
        int32_t b01 = pSrcB[(j + 0) * P + (k + 1)];
        int32_t b02 = pSrcB[(j + 0) * P + (k + 2)];
        int32_t b03 = pSrcB[(j + 0) * P + (k + 3)];
        int32_t b10 = pSrcB[(j + 1) * P + (k + 0)];
        int32_t b11 = pSrcB[(j + 1) * P + (k + 1)];
        int32_t b12 = pSrcB[(j + 1) * P + (k + 2)];
        int32_t b13 = pSrcB[(j + 1) * P + (k + 3)];
        // sum00 += a00*b00 + a01*b10;
        // sum01 += a00*b01 + a01*b11;
        // sum02 += a00*b02 + a01*b12;
        // sum03 += a00*b03 + a01*b13;
        // sum10 += a10*b00 + a11*b10;
        // sum11 += a10*b01 + a11*b11;
        // sum12 += a10*b02 + a11*b12;
        // sum13 += a10*b03 + a11*b13;
        sum00 += a00*b00;
        sum10 += a10*b00;
        sum01 += a00*b01;
        sum11 += a10*b01;
        sum02 += a00*b02;
        sum12 += a10*b02;
        sum03 += a00*b03;
        sum13 += a10*b03;
        sum00 += a01*b10;
        sum10 += a11*b10;
        sum01 += a01*b11;
        sum11 += a11*b11;
        sum02 += a01*b12;
        sum12 += a11*b12;
        sum03 += a01*b13;
        sum13 += a11*b13;
      }
      pDstC[(i + 0) * P + k + 0] = sum00;
      pDstC[(i + 0) * P + k + 1] = sum01;
      pDstC[(i + 0) * P + k + 2] = sum02;
      pDstC[(i + 0) * P + k + 3] = sum03;
      pDstC[(i + 1) * P + k + 0] = sum10;
      pDstC[(i + 1) * P + k + 1] = sum11;
      pDstC[(i + 1) * P + k + 2] = sum12;
      pDstC[(i + 1) * P + k + 3] = sum13;
    }
    for (i = 0; i < 2 * shift_id; i += 2) {
      int32_t sum00 = 0;
      int32_t sum01 = 0;
      int32_t sum02 = 0;
      int32_t sum03 = 0;
      int32_t sum10 = 0;
      int32_t sum11 = 0;
      int32_t sum12 = 0;
      int32_t sum13 = 0;
      for (j = 0; j < N; j += 2) {
        int32_t a00 = pSrcA[(i + 0) * N + (j + 0)];
        int32_t a01 = pSrcA[(i + 0) * N + (j + 1)];
        int32_t a10 = pSrcA[(i + 1) * N + (j + 0)];
        int32_t a11 = pSrcA[(i + 1) * N + (j + 1)];
        int32_t b00 = pSrcB[(j + 0) * P + (k + 0)];
        int32_t b01 = pSrcB[(j + 0) * P + (k + 1)];
        int32_t b02 = pSrcB[(j + 0) * P + (k + 2)];
        int32_t b03 = pSrcB[(j + 0) * P + (k + 3)];
        int32_t b10 = pSrcB[(j + 1) * P + (k + 0)];
        int32_t b11 = pSrcB[(j + 1) * P + (k + 1)];
        int32_t b12 = pSrcB[(j + 1) * P + (k + 2)];
        int32_t b13 = pSrcB[(j + 1) * P + (k + 3)];
        // sum00 += a00*b00 + a01*b10;
        // sum01 += a00*b01 + a01*b11;
        // sum02 += a00*b02 + a01*b12;
        // sum03 += a00*b03 + a01*b13;
        // sum10 += a10*b00 + a11*b10;
        // sum11 += a10*b01 + a11*b11;
        // sum12 += a10*b02 + a11*b12;
        // sum13 += a10*b03 + a11*b13;
        sum00 += a00*b00;
        sum10 += a10*b00;
        sum01 += a00*b01;
        sum11 += a10*b01;
        sum02 += a00*b02;
        sum12 += a10*b02;
        sum03 += a00*b03;
        sum13 += a10*b03;
        sum00 += a01*b10;
        sum10 += a11*b10;
        sum01 += a01*b11;
        sum11 += a11*b11;
        sum02 += a01*b12;
        sum12 += a11*b12;
        sum03 += a01*b13;
        sum13 += a11*b13;
      }
      pDstC[(i + 0) * P + k + 0] = sum00;
      pDstC[(i + 0) * P + k + 1] = sum01;
      pDstC[(i + 0) * P + k + 2] = sum02;
      pDstC[(i + 0) * P + k + 3] = sum03;
      pDstC[(i + 1) * P + k + 0] = sum10;
      pDstC[(i + 1) * P + k + 1] = sum11;
      pDstC[(i + 1) * P + k + 2] = sum12;
      pDstC[(i + 1) * P + k + 3] = sum13;
    }
  }
}
