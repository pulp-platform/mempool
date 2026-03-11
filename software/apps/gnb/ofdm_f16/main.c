// Copyright 2022 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Author: Marco Bertuletti, ETH Zurich

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Mempool runtime libraries */
#include "builtins_v2.h"
#include "dma.h"
#include "encoding.h"
#include "printf.h"
#include "runtime.h"
#include "synchronization.h"

#include "data_ofdm_f16.h"

// CFFT Parameters
#define SCHEDULED
#define FOLDED_TWIDDLES
#define BITREVERSETABLE
#define ASM
#define N_FFTs_COL 4
#define N_FFTs_ROW (N_RX / N_FFTs_COL)
// CMATMUL Parameters
#define NUM_COPIES (NUM_BANKS / (N_BEAMS * N_RX))
#define dim_M (N_BEAMS)
#define dim_N (N_RX)
#define dim_P (N_SC)

#define ROUNDS 3
dump(checkpoint, 1);

#include "baremetal/mempool_cfft_q16_bitreversal.h"
#include "baremetal/mempool_cmatmul_f16.h"
#include "baremetal/mempool_radix4_cfft_butterfly_f16.h"
#include "baremetal/mempool_radix4_cfft_f16p.h"

uint32_t arrival_index __attribute__((section(".l1_prio")));
__fp16 l1_pBF_Coef_folded[2 * BANKING_FACTOR * NUM_CORES]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));

__fp16 l1_pFFT_Src[N_FFTs_ROW * 8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_pFFT_Dst[N_FFTs_ROW * 8 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_src[6 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
__fp16 l1_twiddleCoef_f16_dst[6 * NUM_BANKS]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));
uint16_t l1_BitRevIndexTable[BITREVINDEXTABLE_LENGTH]
    __attribute__((aligned(4 * NUM_BANKS), section(".l1_prio")));

///////////////////////////////////////////////////////////////////////////////////////////////////
/* MAIN */
int main() {
  uint32_t core_id = mempool_get_core_id();
  uint32_t num_cores = mempool_get_core_count();
  mempool_barrier_init(core_id);

  /* INITIALIZATION */
  mempool_start_benchmark();
  if (core_id == 0) {
    // Each FFT is folded over 4 memory rows
    // Each memory row is 2 * NUM_BANKS samples
    __atomic_store_n(&arrival_index, 0, __ATOMIC_RELAXED);
    dma_memcpy_blocking(l1_pFFT_Src, l2_pFFT_Src,
                        (N_RX * N_SC) * sizeof(int32_t));
    dma_memcpy_blocking(l1_BitRevIndexTable, l2_BitRevIndexTable,
                        BITREVINDEXTABLE_LENGTH * sizeof(int16_t));
    for (uint32_t i = 0; i < BANKING_FACTOR * NUM_CORES; i += dim_M * dim_N) {
      dma_memcpy_blocking(&l1_pBF_Coef_folded[2 * i], l2_pBF_Coef,
                          dim_M * dim_N * sizeof(int32_t));
    }
    for (uint32_t i = 0; i < N_FFTs_COL; i++) {
      dma_memcpy_blocking(l1_twiddleCoef_f16_src + (2 * i * NUM_BANKS),
                          l2_twiddleCoef_f16, 3 * (N_SC / 4) * sizeof(int32_t));
    }
  }
  mempool_barrier(num_cores);
  mempool_stop_benchmark();
  dump_checkpoint(0);

  /* FFT */
  mempool_start_benchmark();
  uint32_t CORES_USED = (N_SC / 4) / BANKING_FACTOR;
  // Distribute FFTs over columns
  mempool_radix4_cfft_f16p_scheduler(
      l1_pFFT_Src, l1_pFFT_Dst, N_SC, N_FFTs_ROW, N_FFTs_COL,
      l1_twiddleCoef_f16_src, l1_twiddleCoef_f16_dst, l1_BitRevIndexTable,
      BITREVINDEXTABLE_LENGTH, 1, CORES_USED);
  mempool_log_barrier(2, core_id);
  mempool_stop_benchmark();
  dump_checkpoint(1);

  /* BEAMFORMING */
  mempool_start_benchmark();
  cmatmul_4x4_f16p(l1_pBF_Coef_folded, l1_pFFT_Src, l1_pFFT_Dst, dim_M, dim_N,
                   dim_P, core_id, num_cores);
  mempool_stop_benchmark();
  dump_checkpoint(2);

  mempool_start_benchmark();
  // Transfer and synchronization
  if ((num_cores - 1) ==
      __atomic_fetch_add(&arrival_index, 1, __ATOMIC_RELAXED)) {
    dma_memcpy_blocking(l1_pFFT_Src, l2_pFFT_Src,
                        (N_RX * N_SC) * sizeof(int32_t));
    dma_memcpy_blocking(l2_pBF_Dst, l1_pFFT_Dst,
                        (N_RX * N_SC) * sizeof(int32_t));
    for (uint32_t i = 0; i < N_FFTs_COL; i++) {
      dma_memcpy_blocking(l1_twiddleCoef_f16_src + (2 * i * NUM_BANKS),
                          l2_twiddleCoef_f16, 3 * (N_SC / 4) * sizeof(int32_t));
    }
    __atomic_store_n(&arrival_index, 0, __ATOMIC_RELAXED);
    __sync_synchronize(); // Full memory barrier
    wake_up_all();
  }
  mempool_wfi();
  mempool_stop_benchmark();
  dump_checkpoint(3);

  return 0;
}
